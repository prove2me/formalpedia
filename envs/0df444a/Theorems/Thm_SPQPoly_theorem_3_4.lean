-- Prove2me | Theorems.Thm_SPQPoly_theorem_3_4
-- name    : SPQPoly.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:41.889906+00:00
-- url     : https://prove2.me/theorems/704dfb21-3e62-48e8-88ca-43c9164953ef
-- title:
--   Theorem 3.4 — $N^{SPQ}_{n,d}\setminus\Sigma^{SPQ}_{n,d}\neq\emptyset$ for $n\ge2,d\ge6$ and for $n\ge3,d\ge4$ (corrected: d even)
-- statement:
--   Let $n,d$ be natural numbers with $n\ge2$ and $d\ge6$, or $n\ge3$ and $d\ge4$. Then:
--
--   1. if $d$ is even, $N^{SPQ}_{n,d}\setminus\Sigma^{SPQ}_{n,d}\neq\emptyset$: some SPQ polynomial of degree exactly $d$ in $n$ variables is nonnegative but not a sum of squares;
--   2. for every such $d$, even or odd, some SPQ polynomial of degree at most $d$ in $n$ variables is nonnegative but not a sum of squares.
--
--   Together with Theorems 3.2 and 3.3 this gives the "only if" direction of Theorem 3.1 in every degree and dimension.
--
--   Differences from the source:
--   - correction: N^SPQ_{n,d} \ Σ^SPQ_{n,d} nonempty for every d in the range → for degree exactly d, only for even d; reason: for odd d no polynomial of exact degree d is nonnegative, e.g. (n, d) = (2, 7) gives N^SPQ_{2,7} = ∅
--   - reading: degree d → total degree exactly d (first conjunct); reason: the paper does not fix the reading of degree d
--   - generalization: one reading of degree d → also the degree-at-most-d reading, for every d in the range (second conjunct); reason: the conjunction specializes to either reading
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.4, p.13

import Mathlib
import Definitions.Def_SPQPoly_NSPQ
import Definitions.Def_SPQPoly_SigmaSPQ
import Definitions.Def_SPQPoly_NSPQle
import Definitions.Def_SPQPoly_SigmaSPQle

open MvPolynomial

namespace SPQPoly

/-- **Theorem 3.4 (corrected: `d` even for the exact-degree reading): nonnegative SPQ
polynomials that are not sos in higher degrees and dimensions.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.4, p.13: "For n ≥ 2 and d ≥ 6, and for n ≥ 3 and d ≥ 4, the set
N^SPQ_{n,d} \ Σ^SPQ_{n,d} is nonempty."

For `n ≥ 2, d ≥ 6` and for `n ≥ 3, d ≥ 4`: if `d` is even, some SPQ polynomial of total degree
exactly `d` in `n` variables is nonnegative and not sos; and, for every such `d` (even or odd),
some SPQ polynomial of total degree at most `d` is nonnegative and not sos.

**Formalization Note.** Correction: with "degree d" read as exact total degree, the printed claim
is false for odd `d` (e.g. `(n, d) = (2, 7)`: a polynomial of odd degree takes negative values,
so `N^SPQ_{2,7} = ∅`), so that reading carries `Even d`. The "≤ d" reading needs no correction
and is stated for every `d`. -/
theorem theorem_3_4 (n d : ℕ) (h : (2 ≤ n ∧ 6 ≤ d) ∨ (3 ≤ n ∧ 4 ≤ d)) :
    (Even d → (NSPQ n d \ SigmaSPQ n d).Nonempty) ∧
      (NSPQle n d \ SigmaSPQle n d).Nonempty := by sorry

end SPQPoly
