-- Prove2me | Theorems.Thm_PI_QnHermHaar_mvC
-- name    : PI.QnHermHaar.mvC
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:09.683801+00:00
-- url     : https://prove2.me/theorems/52f27157-f241-497f-993e-7c2d1b3d33a3
-- title:
--   Qn Herm Haar: mv C
-- statement:
--   The Qn Herm Haar construction uses the mv C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L126-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HermitianHaarMeasure/NestedMinorExpansionOneZero.lean#L126-L134

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianHaarMeasure_NestedMinorExpansionOneZero
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

theorem PI.QnHermHaar.mvC (hMV : MoveVec) {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A) (y : Fin n → A)
    (hGl : GlRel E) (hL : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0)
    (hC : ∀ a b, y a * y b = y b * y a) (a : Fin t → Fin n) (b : Fin (t + 1) → Fin n) (w : ℂ) :
    ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (y (b j) * qminor E a (b ∘ j.succAbove) w) =
      ∑ j : Fin (t + 1), ((-1 : ℂ) ^ (j : ℕ)) • (qminor E a (b ∘ j.succAbove) (w - 1) * y (b j)) := by sorry
