-- Prove2me | Theorems.Thm_SPQPoly_p33_multiplier_sos
-- name    : SPQPoly.p33_multiplier_sos
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:09.464682+00:00
-- url     : https://prove2.me/theorems/6cf142a1-2198-4d47-a9c1-e8b19e612ea5
-- title:
--   Theorem 3.3, proof — $(x_1^2+x_2^2+x_3^2)\,p(x)$ is a sum of squares
-- statement:
--   For the polynomial $p$ of Theorem 3.3,
--   $$
--   (x_1^2+x_2^2+x_3^2)\,p(x)
--   $$
--   is a sum of squares of polynomials.
--
--   Since the multiplier is positive away from the origin and $p(0)=9/4>0$, this certifies that $p$ is nonnegative.
--
--   Differences from the source: none.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.3, proof, p.12

import Mathlib
import Definitions.Def_SPQPoly_p33

open MvPolynomial

namespace SPQPoly

/-- **`(x₁² + x₂² + x₃²)·p(x)` is a sum of squares, for the polynomial of Theorem 3.3.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.3, proof, p.12: "Next, we prove that p(x) is nonnegative by showing that the
polynomial (x1^2 + x2^2 + x3^2) p(x) is sos."

**Formalization Note.** `p` is `p33`, `x₁, x₂, x₃` are `X 0, X 1, X 2`; sos is `IsSumSq`. -/
theorem p33_multiplier_sos : IsSumSq ((X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2) * p33) := by sorry

end SPQPoly
