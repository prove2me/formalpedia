-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_zero_not_relativeMinimumDistance
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.zero_not_relativeMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:38:49.715638+00:00
-- url     : https://prove2.me/theorems/cfa7c4a3-15a4-4f4e-a32c-22de86a4180c
-- title:
--   BH12 Even Family: zero not relative Minimum Distance
-- statement:
--   No relative minimum-distance claim is fabricated at the empty endpoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L713-L716
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L713-L716

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.zero_not_relativeMinimumDistance (d : Nat) :
    ¬ RelativeMinimumDistance (family 0).evenCode.dual (family 0).rowCode.dual d := by sorry
