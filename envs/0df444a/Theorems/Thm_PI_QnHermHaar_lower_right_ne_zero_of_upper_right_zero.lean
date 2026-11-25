-- Prove2me | Theorems.Thm_PI_QnHermHaar_lower_right_ne_zero_of_upper_right_zero
-- name    : PI.QnHermHaar.lower_right_ne_zero_of_upper_right_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:38:33.481965+00:00
-- url     : https://prove2.me/theorems/adf9b808-efee-520a-8a07-911f612fdc59
-- title:
--   Qn Herm Haar: lower right ne zero of upper right zero
-- statement:
--   The Qn Herm Haar construction uses the lower right ne zero of upper right zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/LowerRightNeZeroOfUpperRightZero.lean#L135-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/LowerRightNeZeroOfUpperRightZero.lean#L135-L198

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_LowerRightNeZeroOfUpperRightZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.QnHermHaar
open Formalism.REAL Formalism.FourierDecayAlt.Q

theorem PI.QnHermHaar.lower_right_ne_zero_of_upper_right_zero (hSM : StarMinor) (hMV : MoveVec) (hMC : MoveCov) {A : Type} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] {m : ℕ}
    (E : Fin m → Fin m → A) (Y Yb : Fin m → A) (x xb : Fin m → ℂ) (ε : Fin m → ℤˣ) (hGl : GlRel E)
    (hE : ∀ a b, star (E a b) = (((ε a * ε b : ℤˣ) : ℤ) : A) * E b a)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (hYbYb : ∀ a b, Yb a * Yb b = Yb b * Yb a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hLYb : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0)
    (hYb : ∀ c, Yb c = ((ε c : ℤ) : ℂ) • star (Y c)) (hxb : ∀ c, xb c = ((ε c : ℤ) : ℂ) * star (x c))
    (u : ℂ) :
    star (tA E Y Yb x xb u 1 1) = tA E Y Yb x xb (star u) 1 1 := by sorry
