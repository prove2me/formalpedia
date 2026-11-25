-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_form_Jpq
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.form_Jpq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:23:56.816835+00:00
-- url     : https://prove2.me/theorems/c3e5efdb-8fab-4446-b6e5-e4b12c413cd5
-- title:
--   Slope Test Remaining Choices: form Jpq
-- statement:
--   The Slope Test Remaining Choices construction uses the form Jpq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/SylvesterLe.lean#L12-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/SylvesterLe.lean#L12-L17

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix

theorem PI.AutLzFinite.SlopeTestRemainingChoices.form_Jpq (p q : ℕ) (y : Fin p ⊕ Fin q → ℂ) :
    star y ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ y) =
      (∑ i, star (y (Sum.inl i)) * y (Sum.inl i)) - ∑ j, star (y (Sum.inr j)) * y (Sum.inr j) := by sorry
