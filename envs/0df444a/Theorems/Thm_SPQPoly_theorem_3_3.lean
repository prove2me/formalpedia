-- Prove2me | Theorems.Thm_SPQPoly_theorem_3_3
-- name    : SPQPoly.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:41.425302+00:00
-- url     : https://prove2.me/theorems/633abcae-2fa2-4375-b9d6-2e565c3e7642
-- title:
--   Theorem 3.3 — the quartic $p$ lies in $N^{SPQ}_{3,4}\setminus\Sigma^{SPQ}_{3,4}$
-- statement:
--   The trivariate quartic polynomial
--   $$
--   p(x)=x_1^4+2x_1^2+x_2^4+2x_2^2+x_3^4+2x_3^2+\frac94+8x_1x_2+8x_1x_3+8x_2x_3
--   $$
--   belongs to $N^{SPQ}_{3,4}\setminus\Sigma^{SPQ}_{3,4}$: it is SPQ, of degree $4$, nonnegative on $\mathbb R^3$, and not a sum of squares.
--
--   It is the second minimal counterexample behind the "only if" direction of Theorem 3.1.
--
--   **Formalization Note** Degree $4$ is total degree exactly $4$, which also gives membership in the "at most $4$" sets.
--
--   Differences from the source:
--   - reading: N^SPQ_{3,4}, Σ^SPQ_{3,4} (degree 4) → total degree exactly 4; reason: the paper does not fix the reading of degree d; p has total degree exactly 4, so this implies the degree-at-most-4 reading
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.3, p.9

import Mathlib
import Definitions.Def_SPQPoly_p33
import Definitions.Def_SPQPoly_NSPQ
import Definitions.Def_SPQPoly_SigmaSPQ

open MvPolynomial

namespace SPQPoly

/-- **Theorem 3.3: a nonnegative trivariate quartic SPQ polynomial that is not sos.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.3, p.9: "The trivariate quartic polynomial
p(x) = x1^4 + 2x1^2 + x2^4 + 2x2^2 + x3^4 + 2x3^2 + 9/4 + 8x1x2 + 8x1x3 + 8x2x3 belongs to
N^SPQ_{3,4} \ Σ^SPQ_{3,4}."

**Formalization Note.** Membership in `NSPQ 3 4` means: SPQ, total degree exactly `4`, and
nonnegative on `ℝ³`; non-membership in `SigmaSPQ 3 4` then means not `IsSumSq`. -/
theorem theorem_3_3 : p33 ∈ NSPQ 3 4 \ SigmaSPQ 3 4 := by sorry

end SPQPoly
