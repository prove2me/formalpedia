-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_FPw_gaussianInner_monomial_high
-- name    : ReciprocityTheory.ChartRestriction.G.I2.FPw.gaussianInner_monomial_high
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:28:58.648463+00:00
-- url     : https://prove2.me/theorems/1c35f1e9-0181-5fb5-b0d3-e3d859bb0d44
-- title:
--   FPw: gaussian Inner monomial high
-- statement:
--   The FPw construction uses the gaussian Inner monomial high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaIPZeroRight.lean#L75-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/FourierProjections/PaIPZeroRight.lean#L75-L89

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaPolyTranslate
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight
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

theorem ReciprocityTheory.ChartRestriction.G.I2.FPw.gaussianInner_monomial_high {q c : ℕ} (hq : 1 ≤ q) {m : ι →₀ ℕ} (hm : m ∉ paS c)
    {G : EuclideanSpace ℂ ι → ℂ} (hG : G ∈ paPoly c) : paIP q (paMono m) G = 0 := by sorry
