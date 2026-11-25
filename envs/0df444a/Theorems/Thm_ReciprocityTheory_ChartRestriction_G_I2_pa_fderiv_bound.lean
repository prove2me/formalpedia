-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_fderiv_bound
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_fderiv_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:22:00.120226+00:00
-- url     : https://prove2.me/theorems/1ac4213c-cc4a-44b6-a6d9-28128a9ab884
-- title:
--   I2: pa fderiv bound
-- statement:
--   The I2 construction uses the pa fderiv bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L135-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L135-L142

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

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_fderiv_bound {κ : Type} (G : κ → EuclideanSpace ℂ ι → ℂ) (hG : ∀ k, Differentiable ℂ (G k))
    (R : ℝ) (u : κ → ℝ) (hu : ∀ k v, ‖v‖ ≤ R + 1 → ‖G k v‖ ≤ u k) (j : ι) :
    ∀ k y, ‖y‖ ≤ R → ‖fderiv ℂ (G k) y (EuclideanSpace.single j 1)‖ ≤ u k := by sorry
