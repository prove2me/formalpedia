-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_coe_extensionCoefficientLinearEquiv_apply
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.coe_extensionCoefficientLinearEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:27:47.0352+00:00
-- url     : https://prove2.me/theorems/f4d3a708-6da0-46f2-b27e-b8d0d5958ea4
-- title:
--   BH12 Even Family: coe extension Coefficient Linear Equiv apply
-- statement:
--   The BH12 Even Family construction uses the coe extension Coefficient Linear Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1128-L1132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L1128-L1132

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.coe_extensionCoefficientLinearEquiv_apply {q : Nat}
    (a : OddRow q) (c : Sum Unit EvenRow → ZMod 2) :
    ((extensionCoefficientLinearEquiv a c : (singleOddExtensionCode a).carrier) :
      Word (ZMod 2) (Column q)) = extensionCombination a c := by sorry

attribute [defeq] QEC.Distillation.Triorthogonal.BH12EvenFamily.coe_extensionCoefficientLinearEquiv_apply
