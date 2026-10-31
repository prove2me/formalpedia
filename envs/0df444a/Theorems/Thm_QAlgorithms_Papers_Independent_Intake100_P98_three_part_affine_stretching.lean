-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P98_three_part_affine_stretching
-- name    : QAlgorithms.Papers.Independent.Intake100.P98.three_part_affine_stretching
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:10:24.701224+00:00
-- url     : https://prove2.me/theorems/eae410e8-7773-4858-838e-d1f36814bef3
-- title:
--   Remark 5.2, equation (39): three-part affine stretching
-- statement:
--   Let $\lambda,\mu,\nu$ be partitions with at most three parts, padded by zeros, with $|\lambda|+|\mu|=|\nu|$ and $\lambda_i,\mu_i\le\nu_i$. Assume also $c^\nu_{\lambda\mu}>0$. For every positive integer $N$,
--
--   $$
--   c^{N\nu}_{N\lambda\,N\mu}=1+N\bigl(c^\nu_{\lambda\mu}-1\bigr).
--   $$
--
--   Subtraction is in the integers. This is the supported three-part affine stretching identity. The printed sentence omits the support hypothesis; its table argument and the stretching-conjecture context require it. Without it, $\lambda=\mu=(1,1,0)$ and $\nu=(3,1,0)$ have coefficient zero, making the asserted right side negative at $N=2$. This explicit source correction requires independent moderation.
-- source:
--   A polynomiality property for Littlewood-Richardson coefficients, arXiv:math/0308101v2, PDF p. 13, Remark 5.2, equation (39): three-part affine stretching

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P98

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P98

open QAlgorithms.Papers.Independent.Frontier30.P19

attribute [local instance] Classical.propDecidable

/-- Remark 5.2, (39), PDF p.13, corrected supported version.
Printed: no support guard. Changed: c>0, implicit in its nonzero-support table
argument and in Conjecture 1.1. Why: lambda=mu=(1,1,0), nu=(3,1,0) has c=0,
and at N=2 the printed RHS is -1. Subtraction here is in Z, never truncated N.
No inference is made from erroneous rows kappa13--14. Independent moderation
must audit this source correction. -/
theorem three_part_affine_stretching (x : Coordinates 3 → ℕ)
    (hx : IntegralDomain x) (hsupport : 0 < paddedLRCoefficient x) :
    ∀ N : ℕ, 0 < N →
      (paddedLRCoefficient (stretch x N) : ℤ) = 1 + (N : ℤ) * ((paddedLRCoefficient x : ℤ) - 1) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P98

end
