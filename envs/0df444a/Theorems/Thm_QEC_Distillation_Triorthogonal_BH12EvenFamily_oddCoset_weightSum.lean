-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_oddCoset_weightSum
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCoset_weightSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:06:09.919112+00:00
-- url     : https://prove2.me/theorems/bf328037-068d-4a09-bdc5-e3e0a9460a6d
-- title:
--   BH12 Even Family: odd Coset weight Sum
-- statement:
--   The BH12 Even Family construction uses the odd Coset weight Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L966-L987
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L966-L987

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
set_option maxHeartbeats 800000

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.oddCoset_weightSum {A : Type*} [AddCommMonoid A]
    {q : Nat} (a : OddRow q) (f : Nat → A) :
    oddCosetWeightSum a f = 2 • f 7 + 6 • f (3 + 4 * q) := by sorry
