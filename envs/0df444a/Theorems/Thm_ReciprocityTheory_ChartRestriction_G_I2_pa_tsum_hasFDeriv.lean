-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_tsum_hasFDeriv
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_tsum_hasFDeriv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:08:52.507954+00:00
-- url     : https://prove2.me/theorems/5993d4f8-acc8-45a9-9a66-5cb780050fdb
-- title:
--   I2: pa tsum has FDeriv
-- statement:
--   The I2 construction uses the pa tsum has FDeriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L152-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L152-L168

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

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_tsum_hasFDeriv {κ : Type} (G : κ → EuclideanSpace ℂ ι → ℂ) (hG : ∀ k, Differentiable ℂ (G k))
    (hb : ∀ R : ℝ, ∃ u : κ → ℝ, Summable u ∧ ∀ k v, ‖v‖ ≤ R → ‖G k v‖ ≤ u k)
    (x : EuclideanSpace ℂ ι) :
    Summable (fun k => fderiv ℂ (G k) x) ∧
      HasFDerivAt (fun y => ∑' k, G k y) (∑' k, fderiv ℂ (G k) x) x := by sorry
