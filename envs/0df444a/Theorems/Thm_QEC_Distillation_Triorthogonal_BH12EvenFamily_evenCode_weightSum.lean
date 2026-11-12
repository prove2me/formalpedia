-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_evenCode_weightSum
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.evenCode_weightSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:44:36.579453+00:00
-- url     : https://prove2.me/theorems/ccf7f1db-8c88-4f1f-aaf6-fdfc46f4ee5b
-- title:
--   BH12 Even Family: even Code weight Sum
-- statement:
--   The BH12 Even Family construction uses the even Code weight Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L933-L956
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L933-L956

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
set_option maxHeartbeats 800000

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.evenCode_weightSum {A : Type*} [AddCommMonoid A]
    (q : Nat) (f : Nat → A) :
    codeWeightSum (family q).evenCode f =
      f 0 + f 8 + 6 • f (4 + 4 * q) := by sorry
