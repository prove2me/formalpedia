-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_paTh_data
-- name    : ReciprocityTheory.ChartRestriction.G.I2.paTh_data
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:17.05093+00:00
-- url     : https://prove2.me/theorems/2fd4faf3-291c-52c9-856a-5334655a4e90
-- title:
--   I2: pa Th data
-- statement:
--   The I2 construction uses the pa Th data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PaThDiffLe.lean#L87-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/PaThDiffLe.lean#L87-L104

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_CardSupportLeAndSumTwoPowLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PropAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_PaThDiffLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem ReciprocityTheory.ChartRestriction.G.I2.paTh_data (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    Differentiable ℂ (paTh Y q F) ∧ (∀ v, Summable (fun γ : lat Y.b => Y.ka γ * paU q γ F v)) ∧
      ∀ α : ι →₀ ℕ, HasSum (fun γ : lat Y.b => Y.ka γ * paD α (paU q γ F)) (paD α (paTh Y q F)) := by sorry
