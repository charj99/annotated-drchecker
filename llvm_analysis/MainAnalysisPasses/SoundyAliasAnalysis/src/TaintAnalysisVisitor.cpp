//
// Created by machiry on 12/5/16.
//

#include "TaintAnalysisVisitor.h"
#include "PointsToUtils.h"
#include "TaintUtils.h"
#include "CFGUtils.h"

using namespace llvm;
namespace DRCHECKER {

/*#define DEBUG_CALL_INSTR
#define DEBUG_RET_INSTR
#define DEBUG_LOAD_INSTR
#define DEBUG_CAST_INSTR
#define DEBUG
#define DEBUG_BIN_INSTR*/

//#define DEBUG_CALL_INSTR
    /***
         * Get the set of taint flags of the provided value.
         * @param targetVal Value whose taint flags needs to be fetched.
         * @return Set of taint flags of the provided value.
         */
        /* XJJ：获取 currState 中存储的，当前上下文中 targetVal 的污点信息
            若不存在，返回 nullptr
            currState 中存储 “上下文” 到 “<值，污点信息> map” 的映射
            污点信息是 TaintFlag 列表
            class TaintFlag 中的成员包括：值，是否被污染，污染指令链
        */
    std::set<TaintFlag*>* TaintAnalysisVisitor::getTaintInfo(Value *targetVal) {
        return TaintUtils::getTaintInfo(this->currState, this->currFuncCallSites, targetVal);
    }

    // XJJ：获取 globalState 中存储的，当前上下文中指向 targetVal 的指针的污点信息
    void TaintAnalysisVisitor::getPtrTaintInfo(Value *targetVal, std::set<TaintFlag*> &retTaintFlag) {
        std::set<PointerPointsTo*> currValPointsTo;
        // 获取 globalState 中存储的，当前上下文中 targetVal 的指向集
        std::set<PointerPointsTo*> *currPtsTo = PointsToUtils::getPointsToObjects(this->currState, this->currFuncCallSites, targetVal);
        if(currPtsTo != nullptr) {
            currValPointsTo.insert(currPtsTo->begin(), currPtsTo->end());
        }

        // 遍历 targetVal 的指向集中的所有元素，将其污点集合添加到 targetVal 污点集合中
        for(PointerPointsTo *currPtTo: currValPointsTo) {
            std::set<TaintFlag *> *currTaintSet = currPtTo->targetObject->getFieldTaintInfo(currPtTo->dstfieldId);
            if(currTaintSet != nullptr) {
                for(auto a: *currTaintSet) {
                    if(std::find_if(retTaintFlag.begin(), retTaintFlag.end(), [a](const TaintFlag *n) {
                        return  n->isTaintEquals(a);
                    }) == retTaintFlag.end()) {
                        // if not insert the new taint flag into the newTaintInfo.
                        retTaintFlag.insert(a);
                    }
                }
            }
        }
    }
      
    /***
        * Update the taint information of the provided value by the the set of flags.
        * @param targetVal value whose taint information need to be updated.
        * @param targetTaintInfo set containing the new taint flags for the provided value.
        */
    /*
        更新 currState 中存储的，当前上下文中 targetVal 的污点信息
    */
    void TaintAnalysisVisitor::updateTaintInfo(Value *targetVal, std::set<TaintFlag*> *targetTaintInfo) {
        TaintUtils::updateTaintInfo(this->currState, this->currFuncCallSites, targetVal, targetTaintInfo);
    }


    /***
        * Copy taint info from one operand to other operand.
        *
        * @param srcOperand source operand from which the taint info need to be copied.
        * @param targetInstruction Destination instruction to which the taint information needs to be copied to.
        * @param srcTaintInfo set containing taint info that needs to be copied.
        * @param dstTaintInfo [optional] set to which the copied taint info needs to be added
        * @return pointer to the newly created or provided via dstTaintInfo set of taint info
        */
       /*
            把 srcOperand 的污点信息 srcTaintInfo 传播到 targetInstruction，
            并在 dstTaintInfo 非空的时候也将污点信息传播到其中
       */
    std::set<TaintFlag*>* TaintAnalysisVisitor::makeTaintInfoCopy(Value *srcOperand, Instruction *targetInstruction,
                                                                  std::set<TaintFlag*>* srcTaintInfo,
                                                                  std::set<TaintFlag*> *dstTaintInfo) {
        if(srcTaintInfo != nullptr) {
            std::set<TaintFlag *> *newTaintInfo = new std::set<TaintFlag *>();
            bool add_taint = false;
            // 遍历所有源污点
            for (auto currTaint:*srcTaintInfo) {
                add_taint = true;
                if(currTaint->targetInstr != nullptr) {
                    Instruction *srcInstruction = dyn_cast<Instruction>(currTaint->targetInstr);
                    if (srcInstruction != nullptr && targetInstruction != nullptr) {
                        add_taint = BBTraversalHelper::isReachable(srcInstruction, targetInstruction,
                                                                   this->currFuncCallSites);
                    }
                }
                // 如果存在从源污点到目的污点的可达路径，将其添加到集合中
                // 问题：为什么 currTaint->targetInstr == nullptr 时，不用考虑可达性？
                if(add_taint) {
                    // 为 targetInstruction 标记污点信息 currTaint，并在污点链中添加 srcOperand
                    TaintFlag *newTaintFlag = new TaintFlag(currTaint, targetInstruction, srcOperand);
                    newTaintInfo->insert(newTaintInfo->end(), newTaintFlag);
                }
            }
            // if no taint info is propagated.
            if(newTaintInfo->empty()) {
                delete(newTaintInfo);
                newTaintInfo = nullptr;
            }
            // if dstTaintInfo is not null.
            if(dstTaintInfo != nullptr && newTaintInfo != nullptr) {
                // copy all the taint info into dstTaintInfo.
                dstTaintInfo->insert(newTaintInfo->begin(), newTaintInfo->end());
                // delete new taint info
                delete(newTaintInfo);
                // set return value of dstTaintInfo
                newTaintInfo = dstTaintInfo;
            }
            return newTaintInfo;
        }
        return nullptr;
    }

    /***
        * Merge the taint flags of all the values into taint flags of the provided targetInstr.
        *
        * @param srcVals values whose taint values need to be merged.
        * @return Set of new taint flags
        */
       /*
            将 srcVals 中各值的各 TaintFlag 添加到 targetInstr 中 
       */
    std::set<TaintFlag*>* TaintAnalysisVisitor::mergeTaintInfo(std::set<Value *> &srcVals, Value *targetInstr) {

        std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();

        // 枚举所有 srcVals 中的 value
        for(auto currVal:srcVals) {
            // 获取其 taint info
            std::set<TaintFlag*> *currValTaintInfo = getTaintInfo(currVal);
            // we do not have taint info? strip and check
            if(currValTaintInfo == nullptr) {
                currVal = currVal->stripPointerCasts();
            }
            currValTaintInfo = getTaintInfo(currVal);
            // 合并到 newTaintInfo 中
            if(currValTaintInfo != nullptr) {
                // 遍历 currValTaintInfo 中所有 TaintFlag，为 targetInstr 添加该 TaintFlag
                this->makeTaintInfoCopy(targetInstr, dyn_cast<Instruction>(targetInstr),
                                        currValTaintInfo, newTaintInfo);
            }
        }
        // if there is no taint info?
        if(newTaintInfo->empty()) {
            // delete the object.
            delete(newTaintInfo);
            newTaintInfo = nullptr;
        }
        return newTaintInfo;

    }

  /***
        * Add a new taint flag in to the provided set.
        * This function adds only if the taint flag does not already exists in the provided set.
        * @param newTaintInfo set of taint flag to which the new taint flag should be added.
        * @param newTaintFlag new taint flag that needs to be added.
        */
       // 向 newTaintInfo 中添加 newTaintFlag，其中无重复元素
    void TaintAnalysisVisitor::addNewTaintFlag(std::set<TaintFlag*> *newTaintInfo, TaintFlag *newTaintFlag) {
        TaintUtils::addNewTaintFlag(newTaintInfo, newTaintFlag);
    }

    void TaintAnalysisVisitor::visitAllocaInst(AllocaInst &I) {
        // Nothing to do for TaintAnalysis
    }

    // CastInst：把被 cast 的 value 的污点传播到当前指令
    void TaintAnalysisVisitor::visitCastInst(CastInst &I) {
        // handles cast instruction.

        // if the src operand is tainted then the instruction is tainted.

        Value *srcOperand = I.getOperand(0);
        std::set<TaintFlag*>* srcTaintInfo = getTaintInfo(srcOperand);
        if(srcTaintInfo == nullptr) {
            srcOperand = srcOperand->stripPointerCasts();
            srcTaintInfo = getTaintInfo(srcOperand);
        }

        // if there exists some taintflags..propagate them
        if(srcTaintInfo != nullptr) {
            std::set<TaintFlag*> *newTaintInfo = this->makeTaintInfoCopy(srcOperand, &I, srcTaintInfo);
            if(newTaintInfo != nullptr) {
                this->updateTaintInfo(&I, newTaintInfo);
            } else {
#ifdef DEBUG_CAST_INSTR
                dbgs() << "Taint Info cannot be propagated because the current instruction is not reachable from";
                dbgs() << "  tainted source at ";
                I.print(dbgs());
                dbgs() << "\n";
#endif
            }
        }

    }

    // BinaryOperator：合并两个操作数的污点到当前指令
    void TaintAnalysisVisitor::visitBinaryOperator(BinaryOperator &I) {
        // merge taint flag of all the operands.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getOperand(0));
        allVals.insert(allVals.end(), I.getOperand(1));
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
#ifdef DEBUG_BIN_INSTR
            dbgs() << "Propagating taint in binary instruction\n";
#endif
            updateTaintInfo(&I, newTaintInfo);
        }

    }

    // PHINode：合并所有操作数的污点到当前指令
    void TaintAnalysisVisitor::visitPHINode(PHINode &I) {
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumIncomingValues(); i++) {
            allVals.insert(allVals.end(), I.getIncomingValue(i));
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    // SelectInst：合并各分支的污点到当前指令
    void TaintAnalysisVisitor::visitSelectInst(SelectInst &I) {
        /***
         *  Merge taintinfo of all the objects
         *  reaching this select instruction.
         */
        // get all values that need to be merged.
        std::set<Value*> allVals;
        allVals.insert(allVals.end(), I.getTrueValue());
        allVals.insert(allVals.end(), I.getFalseValue());

        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }

    }

    // GetElementPtrInst：合并各个操作数中范围未被限定的 index 的污点到当前指令
    void TaintAnalysisVisitor::visitGetElementPtrInst(GetElementPtrInst &I) {
        // the GEP instruction always computes pointer, which is used to

        // check if one of the operand is tainted?
        // get all values that need to be merged.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumOperands(); i++) {
            Value* currOp = I.getOperand(i);
            Range currRange = this->currState.getRange(currOp);
            if(currRange.isBounded()) {
                // if the range of the index we use is bounded?
                // it may not be bad.
                continue;
            }
            allVals.insert(allVals.end(), currOp);
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    // LoadInst：合并 src 的污点信息和 src 指向的对象的污点信息到当前指令
    // 为什么要包括 src 的污点信息？能够控制从哪里取
    void TaintAnalysisVisitor::visitLoadInst(LoadInst &I) {


#ifdef DEBUG_LOAD_INSTR
        dbgs() << "In taint\n";
        dbgs() << "Taint Analysis Visiting Load Instruction:";
        I.print(dbgs());
        dbgs() << "\n";
#endif
        Value *srcPointer = I.getPointerOperand();
        std::set<TaintFlag*> *srcTaintInfo = getTaintInfo(srcPointer);

        std::set<TaintFlag*> *newTaintInfo = new std::set<TaintFlag*>();

        bool already_stripped = true;
        if(srcTaintInfo == nullptr) {
            already_stripped = false;
            if(getTaintInfo(srcPointer->stripPointerCasts())) {
                srcPointer = srcPointer->stripPointerCasts();
                srcTaintInfo = getTaintInfo(srcPointer);
                already_stripped = true;
            }
        }

        //Copy the taint from tainted pointer.
        // 1. 合并 src 的污点信息到当前指令
        if(srcTaintInfo != nullptr) {
            for(auto currTaintFlag:*srcTaintInfo) {
                TaintFlag *newTaintFlag = new TaintFlag(currTaintFlag, &I, srcPointer);
                TaintAnalysisVisitor::addNewTaintFlag(newTaintInfo, newTaintFlag);
            }
        }

        if(!already_stripped) {
            if(!PointsToUtils::hasPointsToObjects(currState, this->currFuncCallSites, srcPointer)) {
                srcPointer = srcPointer->stripPointerCasts();
            }
        }

        // Get the src points to information.
        std::set<PointerPointsTo*>* srcPointsTo = PointsToUtils::getPointsToObjects(currState,
                                                                                    this->currFuncCallSites,
                                                                                    srcPointer);
        // 若 src 指向的对象非空
        if(srcPointsTo != nullptr) {
            // this set stores the <fieldid, targetobject> of all the objects to which the srcPointer points to.
            
            // 收集所有 unique 的指向对象
            std::set<std::pair<long, AliasObject *>> targetObjects;
            for (PointerPointsTo *currPointsToObj:*srcPointsTo) {
                long target_field = currPointsToObj->dstfieldId;
                AliasObject *dstObj = currPointsToObj->targetObject;
                auto to_check = std::make_pair(target_field, dstObj);
                if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                    targetObjects.insert(targetObjects.end(), to_check);
                }
            }

            // make sure we have some objects.
            assert(targetObjects.size() > 0);

            // 2. 合并 src 指向的对象的污点信息到当前指令
            // add the taint from the corresponding fields of the objects.
            for (auto fieldObject: targetObjects) {
                long currFieldID = fieldObject.first;
                AliasObject *currObject = fieldObject.second;
                // get the taint info of the field.
                std::set<TaintFlag *> *fieldTaintInfo = currObject->getFieldTaintInfo(currFieldID);
#ifdef DEBUG_LOAD_INSTR
                dbgs() << "Trying to get taint from object:" << currObject << " fieldID:" << currFieldID << "\n";
#endif
                // if the field is tainted, add the taint from the field
                // to the result of this instruction.
                if (fieldTaintInfo != nullptr) {
                    this->makeTaintInfoCopy(&I, &I, fieldTaintInfo, newTaintInfo);
                }
            }
        } 
        
        // 若 src 指向的对象为空
        else {
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysis: Src Pointer does not point to any object:";
            srcPointer->print(dbgs());
            dbgs() << "\n";
#endif
        }

        if(newTaintInfo->size()) {
            // okay. Now add the newTaintInfo
#ifdef DEBUG_LOAD_INSTR
            dbgs() << "TaintAnalysis: Updating Taint in LoadInstruction, from:";
            srcPointer->print(dbgs());
            dbgs() << "\n";
#endif
            updateTaintInfo(&I, newTaintInfo);
        } else {
            delete(newTaintInfo);
        }

    }

    // StoreInst：将 src 的污点信息传播到 dst 指向的对象
    void TaintAnalysisVisitor::visitStoreInst(StoreInst &I) {
        Value *srcPointer = I.getValueOperand();
        std::set<TaintFlag *> *srcTaintInfo = getTaintInfo(srcPointer);
        if(srcTaintInfo == nullptr) {
            srcPointer = srcPointer->stripPointerCasts();
            srcTaintInfo = getTaintInfo(srcPointer);
        }

        // if the value, we are trying to store is tainted? Then process, else
        // ignore.
        // 若 src 指向的对象不为空
        if(srcTaintInfo != nullptr) {

            // create newTaintInfo set.
            std::set<TaintFlag *> *newTaintInfo = new std::set<TaintFlag *>();

            bool add_taint;
            for(auto currTaintFlag:*srcTaintInfo) {
                add_taint = true;
                Instruction *currTaintInstr = dyn_cast<Instruction>(&I);
                if(currTaintInstr != nullptr) {
                    // 感觉走到这里 add_taint 就恒真了？
                    add_taint = BBTraversalHelper::isReachable(currTaintInstr, &I, this->currFuncCallSites);
                }
                // 记录 src 的污点信息
                if(add_taint) {
                    TaintFlag *newTaintFlag = new TaintFlag(currTaintFlag, &I, srcPointer);
                    // add the current instruction in the instruction trace.
                    newTaintFlag->addInstructionToTrace(&I);
                    TaintAnalysisVisitor::addNewTaintFlag(newTaintInfo, newTaintFlag);
                }
            }


            // check dstTaintInfo.

            Value *dstPointer = I.getPointerOperand();
            std::set<TaintFlag *> *dstTaintInfo = getTaintInfo(dstPointer);

            bool already_stripped = true;

            if(dstTaintInfo == nullptr) {
                already_stripped = false;
                if(getTaintInfo(dstPointer->stripPointerCasts())) {
                    dstPointer = dstPointer->stripPointerCasts();
                    dstTaintInfo = getTaintInfo(dstPointer);
                    already_stripped = true;
                }
            }

            if(!already_stripped) {
                if(!PointsToUtils::hasPointsToObjects(currState, this->currFuncCallSites, dstPointer)) {
                    dstPointer = dstPointer->stripPointerCasts();
                }
            }

            std::set<PointerPointsTo*>* dstPointsTo = PointsToUtils::getPointsToObjects(currState,
                                                                                        this->currFuncCallSites,
                                                                                        dstPointer);
            // 若 dst 指向的对象不为空
            if(dstPointsTo != nullptr) {

                // Now store the taint into correct fields.
                // this set stores the <fieldid, targetobject> of all the objects to which the dstPointer points to.
                std::set<std::pair<long, AliasObject *>> targetObjects;
                for (PointerPointsTo *currPointsToObj:*dstPointsTo) {
                    long target_field = currPointsToObj->dstfieldId;
                    AliasObject *dstObj = currPointsToObj->targetObject;
                    auto to_check = std::make_pair(target_field, dstObj);
                    if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                        targetObjects.insert(targetObjects.end(), to_check);
                    }
                }

                bool is_added;
                // 将 src 的污点传播到 dst
                // Now try to store the newTaintInfo into all of these objects.
                for(auto newTaintFlag:*newTaintInfo) {
                    is_added = false;
                    for(auto fieldObject:targetObjects) {
                        if(fieldObject.second->addFieldTaintFlag(fieldObject.first, newTaintFlag)) {
                            is_added = true;
                        }
                    }
                    // if the current taint is not added to any object.
                    // delete the newTaint object.
                    if(!is_added) {
                        delete(newTaintFlag);
                    }
                }

            }
            // clean up
            delete(newTaintInfo);
        }

    }

    // The following instructions are ignored.
    // we will deal with them, if we find them
    void TaintAnalysisVisitor::visitVAArgInst(VAArgInst &I) {
        // NO idea how to handle this
        assert(false);
    }

    void TaintAnalysisVisitor::visitVACopyInst(VACopyInst &I) {
        // No idea how to handle this
        assert(false);
    }

    // 把污点传播到函数调用指令的参数
    void TaintAnalysisVisitor::propogateTaintToArguments(std::set<long> &taintedArgs, CallInst &I) {
        assert(taintedArgs.size() > 0);
#ifdef DEBUG_CALL_INSTR
        dbgs() << "Propagating Taint To Arguments.\n";
#endif
        // 遍历需要标记的各参数
        for(auto currArgNo: taintedArgs) {
            Value *currArg = I.getArgOperand(currArgNo);
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Current argument:";
            currArg->print(dbgs());
            dbgs() << "\n";
#endif
            std::set<PointerPointsTo*>* dstPointsTo = PointsToUtils::getPointsToObjects(currState,
                                                                                        this->currFuncCallSites,
                                                                                        currArg);
            if(dstPointsTo == nullptr) {
                currArg = currArg->stripPointerCasts();
                dstPointsTo = PointsToUtils::getPointsToObjects(currState,
                                                                this->currFuncCallSites,
                                                                currArg);
            }

            // 获取当前函数参数指向的对象
            if(dstPointsTo != nullptr) {
                std::set<std::pair<long, AliasObject *>> targetObjects;
                // 遍历每个指向的对象（为实现域敏感，用对象+域 id 表示），
                // 用 targetObjects 记录其中 unique 的部分
                for (PointerPointsTo *currPointsToObj:*dstPointsTo) {
                    long target_field = currPointsToObj->dstfieldId;
                    AliasObject *dstObj = currPointsToObj->targetObject;
                    auto to_check = std::make_pair(target_field, dstObj);
                    if (std::find(targetObjects.begin(), targetObjects.end(), to_check) == targetObjects.end()) {
                        targetObjects.insert(targetObjects.end(), to_check);
                    }
                }

                bool is_added = false;

                assert(targetObjects.size() > 0);

                // 为当前参数创建污点标记，并记录该污点是从函数调用指令 I 引入的
                TaintFlag *newTaintFlag = new TaintFlag(currArg, true);
                newTaintFlag->addInstructionToTrace(&I);

                // 遍历所有该参数指向的对象
                for(auto fieldObject:targetObjects) {
                    // if it is pointing to first field, then taint everything
                    // else taint only corresponding field.
                    // 如果指向的不是第一个域，将对应域标记为污点
                    if(fieldObject.first != 0) {
#ifdef DEBUG_CALL_INSTR
                        dbgs() << "Adding Taint To field ID:"<< fieldObject.first << " of:" << fieldObject.second;
#endif

                        if (fieldObject.second->addFieldTaintFlag(fieldObject.first, newTaintFlag)) {
#ifdef DEBUG_CALL_INSTR
                            dbgs() << ":Success\n";
#endif
                            is_added = true;
                        } else {
#ifdef DEBUG_CALL_INSTR
                            dbgs() << ":Failed\n";
#endif
                        }
                    } 

                    // 如果指向的是第一个域，将所有域标记为污点（为啥？）
                    else {
#ifdef DEBUG_CALL_INSTR
                        dbgs() << "Adding Taint To All fields:"<< fieldObject.first << " of:" << fieldObject.second;
#endif
                        if(fieldObject.second->taintAllFields(newTaintFlag)) {
#ifdef DEBUG_CALL_INSTR
                            dbgs() << ":Success\n";
#endif
                            is_added = true;
                        } else {
#ifdef DEBUG_CALL_INSTR
                            dbgs() << ":Failed\n";
#endif
                        }
                    }
                }
                // if the current taint is not added to any object.
                // delete the newTaint object.
                if(!is_added) {
                    delete(newTaintFlag);
                }

            } else {
                // TODO: raise warning that we do not have any points to information.
#ifdef DEBUG_CALL_INSTR
                dbgs() << "TaintAnalysis: Argument does not have points to information:";
                currArg->print(dbgs());
                dbgs() << "\n";
#endif
            }
        }
    }

    // 为子函数建立上下文
    /*
        将形参中的污点信息传播到实参中
    */
    void TaintAnalysisVisitor::setupCallContext(CallInst &I, Function *currFunction,
                                                std::vector<Instruction *> *newCallContext) {

        // 获取全局数据中存储的新上下文的污点信息
        std::map<Value *, std::set<TaintFlag*>*> *contextTaintInfo = currState.getTaintInfo(newCallContext);

        unsigned int arg_no = 0;

        // 遍历函数调用指令和被调函数的每一个参数
        for(User::op_iterator arg_begin = I.arg_begin(), arg_end = I.arg_end(); arg_begin != arg_end; arg_begin++) {
            Value *currArgVal =(*arg_begin).get();

            if(getTaintInfo(currArgVal) || getTaintInfo(currArgVal->stripPointerCasts())) {
                unsigned int farg_no;
                farg_no = 0;
                std::set<Value*> valuesToMerge;
                // handle pointer casts
                if(!getTaintInfo(currArgVal)) {
                    currArgVal = currArgVal->stripPointerCasts();
                }
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Has Taint Info:" << getTaintInfo(currArgVal)->size() << " taint flags\n";
#endif
                valuesToMerge.clear();
                valuesToMerge.insert(valuesToMerge.end(), currArgVal);

                for(Function::arg_iterator farg_begin = currFunction->arg_begin(), farg_end = currFunction->arg_end();
                    farg_begin != farg_end; farg_begin++) {
                    Value *currfArgVal = &(*farg_begin);
                    if(farg_no == arg_no) {
                        // 将实参的污点信息传播到形参
                        std::set<TaintFlag*> *currArgTaintInfo = mergeTaintInfo(valuesToMerge, &I);
                        // ensure that we didn't mess up.
                        assert(currArgTaintInfo != nullptr);
#ifdef DEBUG_CALL_INSTR
                        // OK, we need to add taint info.
                        dbgs() << "Argument:" << (arg_no + 1) << " has taint info\n";
#endif
                        (*contextTaintInfo)[currfArgVal] = currArgTaintInfo;
                        break;
                    }
                    farg_no++;
                }
            } else {
#ifdef DEBUG_CALL_INSTR
                dbgs() << "Argument:" << (arg_no + 1) << " does not have taint info\n";
#endif
            }
            arg_no++;
        }

    }

    // 将 src 的污点传播到 dst 中
    void TaintAnalysisVisitor::propagateTaintToMemcpyArguments(std::vector<long> &memcpyArgs, CallInst &I) {
#ifdef DEBUG_CALL_INSTR
        dbgs() << "Processing memcpy function\n";
#endif
        // we do not need any special taint handling..because alias takes care of propagating
        // pointer, here we just need to update taint of the arguments.
        // get src operand
        Value *srcOperand = I.getArgOperand((unsigned int) memcpyArgs[0]);
        // get dst operand
        Value *dstOperand = I.getArgOperand((unsigned int) memcpyArgs[1]);

        std::set<Value*> mergeVals;
        mergeVals.insert(srcOperand);

        // 把 src 的污点信息合并到调用 memcpy 函数的指令 I 中
        std::set<TaintFlag*>* newTaintInfo = this->mergeTaintInfo(mergeVals, &I);
        if(newTaintInfo != nullptr) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Trying to memcpy from tainted argument\n";
#endif
            this->updateTaintInfo(dstOperand, newTaintInfo);
        }

    }

    // 处理内部函数
    void TaintAnalysisVisitor::handleKernelInternalFunction(CallInst &I, Function *currFunc) {
        // see if this is a taint initiator function.
        // 如果当前函数是污点入口函数，即 copy_from_user 或 simple_write_to_buffer
        // 将第一个参数 dst，标记为污点
        if(TaintAnalysisVisitor::functionChecker->is_taint_initiator(currFunc)) {
#ifdef DEBUG_CALL_INSTR
            dbgs() << "This function is a taint initiator function:" << currFunc->getName() << "\n";
#endif
            // handling __copy_from_user and its friends.
            std::set<long> taintedArgs = TaintAnalysisVisitor::functionChecker->get_tainted_arguments(currFunc);
            this->propogateTaintToArguments(taintedArgs, I);

        } 
        
        // 如果当前函数是 memcpy 函数（具体定义在 kernelFunctionChecker.cpp 中）
        // 将污点从 src 传播到 dst
        else if(TaintAnalysisVisitor::functionChecker->is_memcpy_function(currFunc)) {
            // Handle memcpy function..
            // get memcpy argument numbers
            std::vector<long> memcpyArgs = TaintAnalysisVisitor::functionChecker->get_memcpy_arguments(currFunc);
            //propagate taint from src to dst.
            this->propagateTaintToMemcpyArguments(memcpyArgs, I);
        } 
        
        // 如果当前函数是 atoi（ascii to integer） 函数（具体定义在 kernelFunctionChecker.cpp 中）
        // 将第一个参数的污点传播到函数返回值
        else if(TaintAnalysisVisitor::functionChecker->is_atoi_function(currFunc)) {
          // This is an atoi like function?
           // if yes? get the taint of the object pointed by the first argument.
            // propagate that to the return value.
            std::set<TaintFlag*> allPointerTaint;
            allPointerTaint.clear();
            this->getPtrTaintInfo(I.getArgOperand(0), allPointerTaint);
            if(!allPointerTaint.empty()) {
                std::set<TaintFlag *> *newTaintSet = this->makeTaintInfoCopy(&I, nullptr, &allPointerTaint);
                this->updateTaintInfo(&I, newTaintSet);
            }

        } 
        
        // 如果当前函数是 sscanf 函数（具体定义在 kernelFunctionChecker.cpp 中）
        // 将第一个参数的污点信息传播到其他非格式化字符串的参数
        // int sscanf(const char *buffer, const char *format, [ argument ] ...); 
        else if(TaintAnalysisVisitor::functionChecker->is_sscanf_function(currFunc)) {
            // This is a sscanf function?
            // if yes? get the taint of the object pointed by the first argument.
            std::set<TaintFlag*> allPointerTaint;
            allPointerTaint.clear();
            this->getPtrTaintInfo(I.getArgOperand(0), allPointerTaint);
            if(!allPointerTaint.empty()) {
                std::set<TaintFlag *> *newTaintSet = this->makeTaintInfoCopy(&I, nullptr, &allPointerTaint);

                std::set<TaintFlag *> addedTaints;

                // now add taint to all objects pointed by the arguments.
                unsigned int arg_idx;
                for (arg_idx = 2; arg_idx < I.getNumArgOperands(); arg_idx++) {
                    Value *argVal = I.getArgOperand(arg_idx);
                    std::set<PointerPointsTo*> *currPtsTo = PointsToUtils::getPointsToObjects(this->currState,
                                                                                              this->currFuncCallSites,
                                                                                              argVal);
                    if(currPtsTo != nullptr) {
                        for(auto currP:*currPtsTo) {
                            for(auto currT:*newTaintSet) {
                                if(currP->targetObject->addFieldTaintFlag(currP->dstfieldId, currT)) {
                                    addedTaints.insert(currT);
                                }
                            }
                        }
                    }
                }

                for(auto currT:*newTaintSet) {
                    if(addedTaints.find(currT) == addedTaints.end()) {
                        delete(currT);
                    }
                }

                delete(newTaintSet);
            }

        } else {
            // TODO (below):
            // untaint all the arguments, depending on whether we are
            // indeed calling kernel internal functions.
        }
    }

    // CallInst：对函数调用指令进行污点传播，过程较为复杂
    VisitorCallback* TaintAnalysisVisitor::visitCallInst(CallInst &I, Function *currFunc,
                                                         std::vector<Instruction *> *oldFuncCallSites,
                                                         std::vector<Instruction *> *callSiteContext) {
        // if this is a kernel internal function.
        // 对于内部函数
        if(currFunc->isDeclaration()) {
            this->handleKernelInternalFunction(I, currFunc);
            return nullptr;
        }

        // 对于非内部函数，为子函数建立上下文，并返回子函数污点分析器
        // else, we need to setup taint context and create a new visitor.
        setupCallContext(I, currFunc, callSiteContext);

        // debugging
        /*if(currFunc->getName() == "m4u_monitor_start") {
            assert(false);
        }*/
        // create a new TaintAnalysisVisitor
        TaintAnalysisVisitor *vis = new TaintAnalysisVisitor(currState, currFunc, callSiteContext);
        return vis;

    }

    // 在 GlobalVisitor 的 visitCallInst 中被调用
    // 把子函数返回值的污点传播到当前指令
    void TaintAnalysisVisitor::stitchChildContext(CallInst &I, VisitorCallback *childCallback) {
        // just connect the taint of the return values.
        TaintAnalysisVisitor *vis = (TaintAnalysisVisitor *)childCallback;
        if(vis->retValTaints.size() > 0 ){
#ifdef DEBUG_CALL_INSTR
            dbgs() << "Stitching return value for call instruction:";
            I.print(dbgs());
            dbgs() << "\n";
#endif
            // create new taint info.
            std::set<TaintFlag*>* newTaintInfo = new std::set<TaintFlag*>();
            for(auto currRetTaint:vis->retValTaints) {
                TaintFlag *newTaintFlag = new TaintFlag(currRetTaint, &I, &I);
                newTaintInfo->insert(newTaintInfo->end(), newTaintFlag);
            }

            //update taint info
            updateTaintInfo(&I, newTaintInfo);
        }
    }

    // ReturnInst：将返回值的污点添加到当前指令
    void TaintAnalysisVisitor::visitReturnInst(ReturnInst &I) {
        // add taint of the return value to the retTaintInfo set.
        Value *targetRetVal = I.getReturnValue();
        if(targetRetVal != nullptr && (getTaintInfo(targetRetVal) || getTaintInfo(targetRetVal->stripPointerCasts()))) {
            // check if pointer casts has a role to play?
            if(!getTaintInfo(targetRetVal)){
                targetRetVal = targetRetVal->stripPointerCasts();
            }
            std::set<TaintFlag*> *currRetTaintInfo = getTaintInfo(targetRetVal);

            for(auto a:*currRetTaintInfo) {
                if(std::find_if(this->retValTaints.begin(), this->retValTaints.end(), [a](const TaintFlag *n) {
                    return  n->isTaintEquals(a);
                }) == this->retValTaints.end()) {
                    // if not insert the new taint flag into the newTaintInfo.
                    this->retValTaints.insert(this->retValTaints.end(), a);
                }
            }

        } else {
#ifdef DEBUG_RET_INSTR
            dbgs() << "Return value:";
            I.print(dbgs());
            dbgs() << ", does not have TaintFlag.\n";
#endif
        }
    }

    // ICmpInst：合并所有操作数的污点到当前指令（可能是因为影响控制流？）
    void TaintAnalysisVisitor::visitICmpInst(ICmpInst &I) {
        // merge taint flag of all the operands.
        std::set<Value*> allVals;
        for(unsigned i=0;i<I.getNumOperands(); i++) {
            Value* currOp = I.getOperand(i);
            allVals.insert(currOp);
        }
        std::set<TaintFlag*> *newTaintInfo = mergeTaintInfo(allVals, &I);
        if(newTaintInfo != nullptr) {
            updateTaintInfo(&I, newTaintInfo);
        }
    }

}