-- Prove2me | Theorems.Thm_SPQPoly_theorem_3_2
-- name    : SPQPoly.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:55.242646+00:00
-- url     : https://prove2.me/theorems/122ed805-b845-45ea-a168-02fc179135d9
-- title:
--   Theorem 3.2 — the sextic $p$ lies in $N^{SPQ}_{2,6}\setminus\Sigma^{SPQ}_{2,6}$
-- statement:
--   The bivariate sextic polynomial
--   $$
--   p(x)=17x_1^6-20x_1^4+7x_1^2+18x_1+18x_2^4-19x_2^2-19x_2+21-20x_1x_2
--   $$
--   belongs to $N^{SPQ}_{2,6}\setminus\Sigma^{SPQ}_{2,6}$: it is SPQ, of degree $6$, nonnegative on $\mathbb R^2$, and not a sum of squares.
--
--   It is one of the two minimal counterexamples behind the "only if" direction of Theorem 3.1.
--
--   **Formalization Note** Degree $6$ is total degree exactly $6$, which also gives membership in the "at most $6$" sets.
--
--   Differences from the source:
--   - reading: N^SPQ_{2,6}, Σ^SPQ_{2,6} (degree 6) → total degree exactly 6; reason: the paper does not fix the reading of degree d; p has total degree exactly 6, so this implies the degree-at-most-6 reading
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.2, p.9

import Mathlib
import Definitions.Def_SPQPoly_p32
import Definitions.Def_SPQPoly_NSPQ
import Definitions.Def_SPQPoly_SigmaSPQ

open MvPolynomial

namespace SPQPoly

/-- **Theorem 3.2: a nonnegative bivariate sextic SPQ polynomial that is not sos.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.2, p.9: "The bivariate sextic polynomial
p(x) = 17x1^6 − 20x1^4 + 7x1^2 + 18x1 + 18x2^4 − 19x2^2 − 19x2 + 21 − 20x1x2 belongs to
N^SPQ_{2,6} \ Σ^SPQ_{2,6}."

**Formalization Note.** Membership in `NSPQ 2 6` means: SPQ, total degree exactly `6`, and
nonnegative on `ℝ²`; non-membership in `SigmaSPQ 2 6` then means not `IsSumSq`. -/
theorem theorem_3_2 : p32 ∈ NSPQ 2 6 \ SigmaSPQ 2 6 := by sorry

end SPQPoly
