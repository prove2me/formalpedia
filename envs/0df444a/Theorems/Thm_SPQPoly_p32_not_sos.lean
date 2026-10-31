-- Prove2me | Theorems.Thm_SPQPoly_p32_not_sos
-- name    : SPQPoly.p32_not_sos
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:16.808222+00:00
-- url     : https://prove2.me/theorems/1cdfbe00-9e8d-4f78-942b-44b6fa861086
-- title:
--   Theorem 3.2, proof — the sextic $p$ is not a sum of squares
-- statement:
--   The polynomial
--   $$
--   p(x)=17x_1^6-20x_1^4+7x_1^2+18x_1+18x_2^4-19x_2^2-19x_2+21-20x_1x_2
--   $$
--   of Theorem 3.2 is **not** a sum of squares: there are no real polynomials $q_1,\dots,q_m$ in $x_1,x_2$ with $p=\sum_i q_i^2$.
--
--   This is the "not sos" half of Theorem 3.2.
--
--   Differences from the source: none.
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.2, proof, pp.9–10

import Mathlib
import Definitions.Def_SPQPoly_p32

open MvPolynomial

namespace SPQPoly

/-- **The polynomial of Theorem 3.2 is not a sum of squares.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.2, proof, pp.9–10: "The proof that p(x) is not sos is done via a separating
hyperplane argument. … This completes the proof that p(x) is not sos."

**Formalization Note.** `p` is `p32`; sos is `IsSumSq` (any finite number of squares of real
polynomials in `x₁, x₂`). -/
theorem p32_not_sos : ¬ IsSumSq p32 := by sorry

end SPQPoly
