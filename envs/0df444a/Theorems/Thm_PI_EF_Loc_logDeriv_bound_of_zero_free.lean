-- Prove2me | Theorems.Thm_PI_EF_Loc_logDeriv_bound_of_zero_free
-- name    : PI.EF.Loc.logDeriv_bound_of_zero_free
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:45.387864+00:00
-- url     : https://prove2.me/theorems/cfa485b2-2a99-40b0-8e50-722eb55253f9
-- title:
--   Loc: log Deriv bound of zero free
-- statement:
--   The Loc construction uses the log Deriv bound of zero free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogDerivBoundOfZeroFree.lean#L8-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogDerivBoundOfZeroFree.lean#L8-L73

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiscIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBoundOfZeroFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology

theorem PI.EF.Loc.logDeriv_bound_of_zero_free (hDL : PI.DiscLog) {g : ℂ → ℂ} {s₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball s₀ R))
    (hz : ∀ z ∈ ball s₀ R, g z ≠ 0) (hb : ∀ z ∈ ball s₀ R, ‖g z‖ ≤ Real.exp M * ‖g s₀‖) :
    ∀ z ∈ closedBall s₀ r, ‖deriv g z / g z‖ ≤ 4 * (r + R) / (R - r) ^ 2 * M := by sorry
