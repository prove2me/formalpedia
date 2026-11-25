-- Prove2me | Theorems.Thm_PI_QnHermHaar_transfer_commutator_one_one
-- name    : PI.QnHermHaar.transfer_commutator_one_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:04:49.803445+00:00
-- url     : https://prove2.me/theorems/0438e1bc-c988-5176-b047-da4bc85a1b32
-- title:
--   Qn Herm Haar: transfer commutator one one
-- statement:
--   The Qn Herm Haar construction uses the transfer commutator one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/LowerRightNeZeroOfUpperRightZero.lean#L76-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/LowerRightNeZeroOfUpperRightZero.lean#L76-L121

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

theorem PI.QnHermHaar.transfer_commutator_one_one (hMV : MoveVec) (hMC : MoveCov) {A : Type} [Ring A] [Algebra ℂ A] {t : ℕ}
    (E : Fin (t + 2) → Fin (t + 2) → A) (Y Yb : Fin (t + 2) → A) (hGl : GlRel E)
    (hYY : ∀ a b, Y a * Y b = Y b * Y a) (hYbYb : ∀ a b, Yb a * Yb b = Yb b * Yb a)
    (hLY : ∀ a b c, E a b * Y c - Y c * E a b = if a = c then -Y b else 0)
    (hLYb : ∀ a b c, E a b * Yb c - Yb c * E a b = if b = c then Yb a else 0)
    (a b : Fin (t + 2)) (w : ℂ) :
    ∑ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
        (qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w * Yb (a.succAbove k) *
          Y (b.succAbove l)) =
      ∑ k : Fin (t + 1), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (k : ℕ) * (-1 : ℂ) ^ (l : ℕ)) •
        (Yb (a.succAbove k) * Y (b.succAbove l) *
          qminor E (a.succAbove ∘ k.succAbove) (b.succAbove ∘ l.succAbove) w) := by sorry
