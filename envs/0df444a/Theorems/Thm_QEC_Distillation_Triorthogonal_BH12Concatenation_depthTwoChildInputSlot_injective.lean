-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildInputSlot_injective
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildInputSlot_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:35:02.112626+00:00
-- url     : https://prove2.me/theorems/0e5faa16-7173-41f9-b32e-8f9932d43f1e
-- title:
--   BH12 Concatenation: depth Two Child Input Slot injective
-- statement:
--   The routed inputs of one child block have pairwise distinct parent sources.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1327-L1333
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1327-L1333

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildInputSlot_injective (q : Nat)
    (child : Fin (bh12OutputCount q)) :
    Function.Injective (depthTwoChildInputSlot q child) := by sorry
