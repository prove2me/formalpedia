-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_pureZLogicalMinimumDistance_two
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.pureZLogicalMinimumDistance_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:06:20.657137+00:00
-- url     : https://prove2.me/theorems/046d1324-4091-4981-9519-1116d0618ddb
-- title:
--   BH12 Even Family: pure ZLogical Minimum Distance two
-- statement:
--   CSS terminology for the exact positive-family pure-`Z` distance statement.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L689-L691
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L689-L691

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.pureZLogicalMinimumDistance_two {q : Nat} (hq : 0 < q) :
    PureZLogicalMinimumDistance (family q).evenCode (family q).rowCode.dual 2 := by sorry
