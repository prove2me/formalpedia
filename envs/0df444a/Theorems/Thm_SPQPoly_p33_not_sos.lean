-- Prove2me | Theorems.Thm_SPQPoly_p33_not_sos
-- name    : SPQPoly.p33_not_sos
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:15.117222+00:00
-- url     : https://prove2.me/theorems/973a618d-a3f6-45e6-87e0-1031c4da90d4
-- title:
--   Theorem 3.3, proof — the quartic $p$ is not a sum of squares
-- statement:
--   The polynomial
--   $$
--   p(x)=x_1^4+2x_1^2+x_2^4+2x_2^2+x_3^4+2x_3^2+\frac94+8x_1x_2+8x_1x_3+8x_2x_3
--   $$
--   of Theorem 3.3 is **not** a sum of squares of real polynomials in $x_1,x_2,x_3$.
--
--   This is the "not sos" half of Theorem 3.3.
--
--   Differences from the source: none.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.3, proof, pp.11–12

import Mathlib
import Definitions.Def_SPQPoly_p33

open MvPolynomial

namespace SPQPoly

/-- **The polynomial of Theorem 3.3 is not a sum of squares.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.3, proof, pp.11–12: "As in the proof of Theorem 3.2, we show that p(x) is not sos
via a separating hyperplane argument. … This completes the proof that p(x) is not sos."

**Formalization Note.** `p` is `p33`; sos is `IsSumSq`. -/
theorem p33_not_sos : ¬ IsSumSq p33 := by sorry

end SPQPoly
