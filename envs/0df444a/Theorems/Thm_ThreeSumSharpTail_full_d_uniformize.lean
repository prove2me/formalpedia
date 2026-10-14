-- Prove2me | Theorems.Thm_ThreeSumSharpTail_full_d_uniformize
-- name    : ThreeSumSharpTail.full_d_uniformize
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T20:30:12.748968+00:00
-- url     : https://prove2.me/theorems/c66b236f-cbfe-4988-b4a1-70cb9d1d65cc
-- title:
--   Thresholded full dimension Exact Triangle time extends to every size
-- statement:
--   For any 0<=delta<=1, natural logarithmic degree and threshold, an actual light-model ExplicitAt solver implies ExactTriangleUniform with the same saving and logarithmic degree. A finite choice program selects the new solver for large sizes and an existing correct solver for bounded small sizes, preserving native polynomial resources and all-size correctness.
-- source:
--   Generic ChooseBySize and monotone-time assembly from accepted Exact Triangle source. The small-size solver is used only on a fixed bounded domain; the large-size exponent comes from the supplied new ExplicitAt proof.

import Definitions.Def_APSP299791_Defs5

theorem ThreeSumSharpTail.full_d_uniformize (δ : ℝ) (e n₀ : ℕ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hex : ThreeSumApsp.Claim.Theorem_19_explicitAt Light.lightModel δ e n₀) :
    ThreeSumApsp.Claim.ExactTriangleUniform Light.lightModel δ e := by sorry
