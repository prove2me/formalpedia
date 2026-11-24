-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_contDiff_of_diff
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_contDiff_of_diff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:12.484633+00:00
-- url     : https://prove2.me/theorems/1175922b-f337-4567-94f0-4cca5f2c8b43
-- title:
--   I2: pa cont Diff of diff
-- statement:
--   The I2 construction uses the pa cont Diff of diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L170-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L170-L181

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

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_contDiff_of_diff {S : EuclideanSpace ℂ ι → ℂ} (hS : Differentiable ℂ S) :
    ContDiff ℂ (⊤ : ℕ∞) S := by sorry
