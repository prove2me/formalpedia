-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12EvenFamily_evenCoefficient_weightSum
-- name    : QEC.Distillation.Triorthogonal.BH12EvenFamily.evenCoefficient_weightSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:44:50.517407+00:00
-- url     : https://prove2.me/theorems/b45e821c-9fbe-43d7-a72a-5856999a538e
-- title:
--   BH12 Even Family: even Coefficient weight Sum
-- statement:
--   The BH12 Even Family construction uses the even Coefficient weight Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L869-L875
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/EvenFamily.lean#L869-L875

import Definitions.Def_QEC_Distillation_Triorthogonal_Transversal
import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12EvenFamily
open Coding
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.Triorthogonal.BH12EvenFamily.evenCoefficient_weightSum {A : Type*} [AddCommMonoid A]
    (q : Nat) (f : Nat → A) :
    (∑ i : Fin 8, f (HammingWeight (evenCombination q (coefficientBits i)))) =
      f 0 + f 8 + 6 • f (4 + 4 * q) := by sorry
