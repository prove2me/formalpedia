-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_pa_iter_tsum
-- name    : ReciprocityTheory.ChartRestriction.G.I2.pa_iter_tsum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:30:38.548159+00:00
-- url     : https://prove2.me/theorems/547c035f-b9cc-5175-b39a-a6a897064532
-- title:
--   I2: pa iter tsum
-- statement:
--   The I2 construction uses the pa iter tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L183-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PropAC.lean#L183-L231

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

theorem ReciprocityTheory.ChartRestriction.G.I2.pa_iter_tsum (n : ℕ) : ∀ {κ : Type} (G : κ → EuclideanSpace ℂ ι → ℂ),
    (∀ k, ContDiff ℂ (⊤ : ℕ∞) (G k)) →
    (∀ R : ℝ, ∃ u : κ → ℝ, Summable u ∧ ∀ k v, ‖v‖ ≤ R → ‖G k v‖ ≤ u k) →
    ∀ (m : Fin n → ι) (x : EuclideanSpace ℂ ι),
      HasSum (fun k => iteratedFDeriv ℂ n (G k) x (fun i => EuclideanSpace.single (m i) 1))
        (iteratedFDeriv ℂ n (fun y => ∑' k, G k y) x (fun i => EuclideanSpace.single (m i) 1)) := by sorry
