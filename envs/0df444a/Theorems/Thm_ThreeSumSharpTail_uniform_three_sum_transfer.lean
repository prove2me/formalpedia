-- Prove2me | Theorems.Thm_ThreeSumSharpTail_uniform_three_sum_transfer
-- name    : ThreeSumSharpTail.uniform_three_sum_transfer
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-13T18:54:00.599997+00:00
-- url     : https://prove2.me/theorems/87e1ae72-5579-4a7e-b1a8-501649499458
-- title:
--   Uniform Exact Triangle exponent transfers to integer 3SUM
-- statement:
--   For any real saving delta<=1, rational r>2-delta/2, and natural logarithmic degree e, a uniform Exact Triangle solver in the actual light model implies EndStatement.ThreeSum.SolvedInTime r. The conclusion includes the original word-RAM finite-program and all-sufficient-word-width semantics. The five existing proved reduction and realization interfaces are actual dependencies.
-- source:
--   Generic reduction and asymptotic proof bodies extracted from ACCEPTED TrulySubquadratic3SUM.threeSum_1999074, submission 7d7091ea-6717-4422-b336-026472ef8a11; the numerical specialization is excluded. Composes CH20 and VW13 Theorem 4.3 with the actual light-model realization and shared EndStatement interface.

import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_ThreeSumSource_ReductionClaims

theorem ThreeSumSharpTail.uniform_three_sum_transfer (δ : ℝ) (r : ℚ) (e : ℕ)
    (hδ : δ ≤ 1) (hr : 2 - δ / 2 < (r : ℝ))
    (hu : ThreeSumApsp.Claim.ExactTriangleUniform Light.lightModel δ e) :
    EndStatement.ThreeSum.SolvedInTime r := by sorry
