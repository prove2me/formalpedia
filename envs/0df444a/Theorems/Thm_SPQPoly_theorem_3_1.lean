-- Prove2me | Theorems.Thm_SPQPoly_theorem_3_1
-- name    : SPQPoly.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:59.239989+00:00
-- url     : https://prove2.me/theorems/dc2569d1-dd78-4d22-af6e-c75c6f3cc8e6
-- title:
--   Theorem 3.1 — $\Sigma^{SPQ}_{n,d}=N^{SPQ}_{n,d}$ iff $n=1$, $d=2$ or $(n,d)=(2,4)$ (corrected: n ≥ 1, d ≥ 2 even)
-- statement:
--   Let $n\ge1$ and let $d\ge2$ be even. Write $N^{SPQ}_{n,d}$ for the nonnegative and $\Sigma^{SPQ}_{n,d}$ for the sum-of-squares SPQ polynomials of degree $d$ in $n$ variables. Then
--   $$
--   \Sigma^{SPQ}_{n,d}=N^{SPQ}_{n,d}\quad\Longleftrightarrow\quad n=1,\ \text{or}\ d=2,\ \text{or}\ (n,d)=(2,4),
--   $$
--   and the same equivalence holds when "degree $d$" is read as "degree at most $d$".
--
--   So restricting to separable plus quadratic structure leaves exactly Hilbert's cases: whenever nonnegative polynomials of degree $d$ in $n$ variables need not be sos, some nonnegative SPQ polynomial is already not sos.
--
--   **Formalization Note** The theorem is a conjunction of two equivalences: one for total degree exactly $d$ (`SigmaSPQ`, `NSPQ`), one for total degree at most $d$ (`SigmaSPQle`, `NSPQle`).
--
--   Differences from the source:
--   - correction: the iff for every (n, d) → hypotheses 1 ≤ n, 2 ≤ d and d even; reason: the printed iff is false at (n, d) = (2, 0) (nonnegative constants are squares, so the sets are equal although no listed case holds), at (2, 5) (a polynomial of odd degree takes negative values, so both exact-degree sets are empty; the degree-≤-5 sets are the degree-≤-4 ones, equal by Hilbert) and at (0, 4) (both sets are empty or constant); the paper itself treats d as even (proof of Theorem 3.4, p.13)
--   - reading: degree d → total degree exactly d (first conjunct); reason: the paper never says whether degree d is exact or an upper bound
--   - generalization: one reading of degree d → both readings: the same iff also for total degree at most d (second conjunct); reason: each direction is strongest in a different reading; the conjunction specializes to either reading
--   - encoding: polynomials p : ℝⁿ → ℝ in x₁, …, xₙ; sos as Σ qᵢ² → MvPolynomial (Fin n) ℝ with variables X 0, …, X (n-1); IsSumSq; reason: Lean convention; same objects
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 3.1, p.9

import Mathlib
import Definitions.Def_SPQPoly_NSPQ
import Definitions.Def_SPQPoly_SigmaSPQ
import Definitions.Def_SPQPoly_NSPQle
import Definitions.Def_SPQPoly_SigmaSPQle

open MvPolynomial

namespace SPQPoly

/-- **Theorem 3.1 (corrected: `n ≥ 1`, `d ≥ 2` even): nonnegative SPQ polynomials of degree `d`
in `n` variables are all sos iff `n = 1`, or `d = 2`, or `(n, d) = (2, 4)`.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 3.1, p.9: "Σ^SPQ_{n,d} = N^SPQ_{n,d} if and only if n = 1, or d = 2, or
(n, d) = (2, 4)."

**Formalization Note.** Correction: the printed iff ranges over all `(n, d)` and is false at
`(2, 0)` (both sets are the nonnegative constants), `(2, 5)` (no polynomial of odd degree is
nonnegative, so both exact-degree sets are empty; the "≤ 5" sets are the "≤ 4" ones, equal by
Hilbert) and `(0, 4)`; the hypotheses `1 ≤ n`, `2 ≤ d`, `Even d` are the minimal correction. The
paper does not fix whether "degree d" means exactly or at most `d`; both readings are stated, as
a conjunction. -/
theorem theorem_3_1 (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d) (hev : Even d) :
    (SigmaSPQ n d = NSPQ n d ↔ (n = 1 ∨ d = 2 ∨ (n = 2 ∧ d = 4))) ∧
    (SigmaSPQle n d = NSPQle n d ↔ (n = 1 ∨ d = 2 ∨ (n = 2 ∧ d = 4))) := by sorry

end SPQPoly
