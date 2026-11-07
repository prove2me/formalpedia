-- Prove2me | Theorems.Thm_QEC_Distillation_DependentBatch_childInputSlot_injective
-- name    : QEC.Distillation.DependentBatch.childInputSlot_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:01:18.620197+00:00
-- url     : https://prove2.me/theorems/a994d545-d748-4622-ac80-17dbeaeb5624
-- title:
--   Dependent Batch: child Input Slot injective
-- statement:
--   Inputs inside one child block come from distinct parent blocks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/DependentBatch.lean#L47-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Core/DependentBatch.lean#L47-L50

import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Core_DependentBatch
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.DependentBatch
open Semantics
open scoped BigOperators
universe u v

theorem QEC.Distillation.DependentBatch.childInputSlot_injective {Parent Port : Type*} (port : Port) :
    Function.Injective (childInputSlot port : Parent → Parent × Port) := by sorry
