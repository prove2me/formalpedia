-- Prove2me | Theorems.Thm_PI_SqfPrimeFactor_W_ana_main
-- name    : PI.SqfPrimeFactor.W.ana_main
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:26:27.810538+00:00
-- url     : https://prove2.me/theorems/0fa8e58b-17d4-4cd0-9d06-a364c67765f0
-- title:
--   W: ana main
-- statement:
--   The W construction uses the ana main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/AnaCore.lean#L73-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarefreePrimeFactor/AnaCore.lean#L73-L137

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PrimesDyadicRS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreePrimeFactor_AnaCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.SqfPrimeFactor PI.SqfPrimeFactor.W
open Finset

theorem PI.SqfPrimeFactor.W.ana_main (hRS : PI.PrimesDyadicRS.Claim) (g r : ℕ) (hr : 100 ≤ r) (hg : 2 ^ 12 ≤ g)
    (S : Finset ℕ) (hS : ∀ p, p ∈ S ↔ p.Prime ∧ r < 2 * p ∧ p + 3 ≤ r) :
    (g : ℝ) ^ r - ∑ p ∈ S, ((g : ℝ) ^ p - g) / p * (g : ℝ) ^ (r - p) ≤
      (1 - 1 / (5 * Real.log r)) * (g : ℝ) ^ r := by sorry
