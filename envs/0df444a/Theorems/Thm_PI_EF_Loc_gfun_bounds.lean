-- Prove2me | Theorems.Thm_PI_EF_Loc_gfun_bounds
-- name    : PI.EF.Loc.gfun_bounds
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:01.26289+00:00
-- url     : https://prove2.me/theorems/5b94e44f-105d-45a3-b31f-99e92bef2fbc
-- title:
--   Loc: gfun bounds
-- statement:
--   The Loc construction uses the gfun bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalAbstract.lean#L42-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LocalAbstract.lean#L42-L106

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

theorem PI.EF.Loc.gfun_bounds (hR' : 0 < R') (hR'R : R' < R)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    (∀ z ∈ closedBall s₀ R, ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * ‖gfun s₀ R Z m h s₀‖) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * Real.log (R / R') ≤ M := by sorry
