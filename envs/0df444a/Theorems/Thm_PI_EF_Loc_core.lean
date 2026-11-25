-- Prove2me | Theorems.Thm_PI_EF_Loc_core
-- name    : PI.EF.Loc.core
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:31.342335+00:00
-- url     : https://prove2.me/theorems/55c466e6-1574-40ed-ab6d-2731bb7d3a51
-- title:
--   Loc: core
-- statement:
--   The Loc construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalAbstract.lean#L108-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalAbstract.lean#L108-L197

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBoundOfZeroFree
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_NormLogDerivReflLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LocalAbstract
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF PI.EF.Loc
open Complex Metric Set Filter Topology
variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}

theorem PI.EF.Loc.core (hDL : PI.DiscLog) (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) (hM : 0 < M)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
      ‖logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by sorry
