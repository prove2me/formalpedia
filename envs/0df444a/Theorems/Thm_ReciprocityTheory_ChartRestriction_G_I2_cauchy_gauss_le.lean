-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_cauchy_gauss_le
-- name    : ReciprocityTheory.ChartRestriction.G.I2.cauchy_gauss_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:28:25.870957+00:00
-- url     : https://prove2.me/theorems/d9f08aae-5bb2-47e5-b849-d98af7d36e89
-- title:
--   I2: cauchy gauss le
-- statement:
--   The I2 construction uses the cauchy gauss le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCauchy.lean#L70-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCauchy.lean#L70-L118

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

theorem ReciprocityTheory.ChartRestriction.G.I2.cauchy_gauss_le {N k : ℕ} (F : (Fin N → ℂ) → ℂ) (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ z, ‖F z‖ ^ 2 * Real.exp (-Real.pi * ∑ i, ‖z i‖ ^ 2) ≤ S) (l : Fin k → Fin N) :
    ‖iteratedFDeriv ℂ k F 0 (fun j => Pi.single (l j) 1)‖ ≤
      Real.sqrt S * (Real.pi * Real.exp 1 * k) ^ ((k : ℝ) / 2) := by sorry
