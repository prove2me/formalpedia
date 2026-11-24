-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_iter_step_bound
-- name    : ReciprocityTheory.ChartRestriction.G.I2.iter_step_bound
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:23.84615+00:00
-- url     : https://prove2.me/theorems/ad53df2d-f2d8-481d-b4b0-40b7534d9c50
-- title:
--   I2: iter step bound
-- statement:
--   The I2 construction uses the iter step bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCauchy.lean#L21-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCauchy.lean#L21-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Metric

theorem ReciprocityTheory.ChartRestriction.G.I2.iter_step_bound {N : ℕ} (F : (Fin N → ℂ) → ℂ) (hF : Differentiable ℂ F) (ρ M : ℝ)
    (hρ : 0 < ρ) : ∀ (k : ℕ) (l : Fin k → Fin N) (x : Fin N → ℂ),
    (∀ y, ∑ i, ‖y i - x i‖ ≤ k * ρ → ‖F y‖ ≤ M) →
    ‖iteratedFDeriv ℂ k F x (fun j => Pi.single (l j) 1)‖ ≤ M / ρ ^ k
  := by sorry
