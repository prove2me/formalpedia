-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_theta__d77fbce164e2
-- name    : P2M_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_theta__d77fbce164e2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:16:38.836481+00:00
-- url     : https://prove2.me/theorems/7e38fa6b-4083-4d8a-ba23-8156e1db2723
-- title:
--   P2 M Reciprocity Theory Chart Restriction G I2 FPw gaussian Inner theta  d77fbce164e2: P2 M Reciprocity Theory Chart Restriction G I2 FPw gaussian Inner theta  d77fbce164e2
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction G I2 FPw gaussian Inner theta  d77fbce164e2 construction uses the P2 M Reciprocity Theory Chart Restriction G I2 FPw gaussian Inner theta  d77fbce164e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean#L165-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaUContinuous.lean#L165-L206

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_HfEqInner
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaUContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical

theorem P2M_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_theta__d77fbce164e2 (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    HasSum (fun γ : lat Y.b => Y.ka γ * paIP q (paU q γ F) G) (paIP q (paTh Y q F) G) := by sorry

alias «ReciprocityTheory».«ChartRestriction».«G».«I2».«FPw».«gaussianInner_theta'» := P2M_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_theta__d77fbce164e2
