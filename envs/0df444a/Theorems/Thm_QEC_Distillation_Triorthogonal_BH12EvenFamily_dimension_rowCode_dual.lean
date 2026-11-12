-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_dimension_rowCode_dual
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_rowCode_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:36:59.094183+00:00
-- url     : https://prove2.me/theorems/cbcd03de-8064-497e-b38e-5bb8e8472635
-- title:
--   BH12 Even Family: dimension row Code dual
-- statement:
--   `dim G⊥ = 2k+5`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L491-L497
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L491-L497

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.dimension_rowCode_dual (q : Nat) :
    Dimension (family q).rowCode.dual = 2 * logicalCount q + 5 := by sorry
