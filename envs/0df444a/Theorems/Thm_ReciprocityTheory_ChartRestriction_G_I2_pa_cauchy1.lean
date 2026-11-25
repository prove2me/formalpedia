-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_cauchy1
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_cauchy1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:44.323027+00:00
-- url     : https://prove2.me/theorems/ac97dfb7-8c29-4b6a-a11e-b0a64fa4bdc4
-- title:
--   I2: pa cauchy1
-- statement:
--   The I2 construction uses the pa cauchy1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L100-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L100-L115

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_RCauchy
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex Metric
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_cauchy1 {H : EuclideanSpace ℂ ι → ℂ} (hH : Differentiable ℂ H) (y : EuclideanSpace ℂ ι)
    (j : ι) {M : ℝ} (hM : ∀ t : ℂ, ‖t‖ = 1 → ‖H (y + t • EuclideanSpace.single j 1)‖ ≤ M) :
    ‖fderiv ℂ H y (EuclideanSpace.single j 1)‖ ≤ M := by sorry
