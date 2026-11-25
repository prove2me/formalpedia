-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_contDiff_of_differentiable
-- name    : ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:04:14.498905+00:00
-- url     : https://prove2.me/theorems/e5c97a62-706c-4a96-9e06-7ae733c136c4
-- title:
--   I2: cont Diff of differentiable
-- statement:
--   The I2 construction uses the cont Diff of differentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCauchy.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/RCauchy.lean#L16-L19

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

theorem ReciprocityTheory.ChartRestriction.G.I2.contDiff_of_differentiable {N : ℕ} {F : (Fin N → ℂ) → ℂ} (hF : Differentiable ℂ F)
    {n : WithTop ℕ∞} : ContDiff ℂ n F := by sorry
