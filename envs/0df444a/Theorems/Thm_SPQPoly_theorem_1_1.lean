-- Prove2me | Theorems.Thm_SPQPoly_theorem_1_1
-- name    : SPQPoly.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:37:06.750984+00:00
-- url     : https://prove2.me/theorems/24a95943-422a-4909-ad2b-88ca17992a27
-- title:
--   Theorem 1.1 (Hilbert) — $\Sigma_{n,d}=N_{n,d}$ iff $n=1$, $d=2$ or $(n,d)=(2,4)$ (corrected: n ≥ 1, d ≥ 2 even)
-- statement:
--   **Hilbert's theorem (1888).** Let $n\ge1$ and let $d\ge2$ be even. Write $N_{n,d}$ for the nonnegative and $\Sigma_{n,d}$ for the sum-of-squares real polynomials of degree $d$ in $n$ variables. Then
--   $$
--   \Sigma_{n,d}=N_{n,d}\quad\Longleftrightarrow\quad n=1,\ \text{or}\ d=2,\ \text{or}\ (n,d)=(2,4),
--   $$
--   and the same equivalence holds when "degree $d$" is read as "degree at most $d$".
--
--   The paper cites this theorem ([20]); it gives the "if" direction of Theorem 3.1, since SPQ polynomials are in particular polynomials.
--
--   **Formalization Note** The theorem is a conjunction of two equivalences: one for the sets of total degree exactly $d$ (`SigmaPoly`, `NPoly`), one for total degree at most $d$ (`SigmaPolyLe` and the published nonnegative cone `NieYangPareto.nonnegCone` over $K=\mathbb R^n$).
--
--   Differences from the source:
--   - correction: the iff for every (n, d) → hypotheses 1 ≤ n, 2 ≤ d and d even; reason: the printed iff is false at (n, d) = (2, 0) (nonnegative constants are squares, so the sets are equal although no listed case holds), at (2, 5) (a polynomial of odd degree takes negative values, so both exact-degree sets are empty; the degree-≤-5 sets are the degree-≤-4 ones, equal by Hilbert) and at (0, 4) (both sets are empty or constant); the paper itself treats d as even (proof of Theorem 3.4, p.13)
--   - reading: degree d → total degree exactly d (first conjunct); reason: the paper never says whether degree d is exact or an upper bound
--   - generalization: one reading of degree d → both readings: the same iff also for total degree at most d (second conjunct); reason: each direction is strongest in a different reading; the conjunction specializes to either reading
--   - encoding: polynomials p : ℝⁿ → ℝ in x₁, …, xₙ; sos as Σ qᵢ² → MvPolynomial (Fin n) ℝ with variables X 0, …, X (n-1); IsSumSq; reason: Lean convention; same objects
-- source:
--   Ahmadi, Dibek & Hall, Sums of Separable and Quadratic Polynomials, arXiv:2105.04766v1, Theorem 1.1 ([20]), p.1

import Mathlib
import Definitions.Def_SPQPoly_NPoly
import Definitions.Def_SPQPoly_SigmaPoly
import Definitions.Def_NieYangPareto_nonnegCone
import Definitions.Def_SPQPoly_SigmaPolyLe

open MvPolynomial

namespace SPQPoly

/-- **Theorem 1.1 (Hilbert, 1888), corrected: `Σ_{n,d} = N_{n,d}` iff `n = 1`, `d = 2` or
`(n, d) = (2, 4)`, for `n ≥ 1` and even `d ≥ 2`.**
Ahmadi, Dibek & Hall, *Sums of Separable and Quadratic Polynomials*, arXiv:2105.04766v1, Theorem 1.1 ([20]), p.1:
"Σn,d = Nn,d if and only if n = 1, or d = 2, or (n, d) = (2, 4)."

For every `n ≥ 1` and every even `d ≥ 2`, the sos polynomials of degree `d` in `n` variables
are exactly the nonnegative ones if and only if `n = 1`, or `d = 2`, or `(n, d) = (2, 4)`; and the
same holds for the polynomials of degree at most `d`.

**Formalization Note.** Correction: the printed iff ranges over all `(n, d)` and is false at
`(2, 0)` (nonnegative constants are squares), `(2, 5)` (no polynomial of odd degree is
nonnegative, so both exact-degree sets are empty) and `(0, 4)`; the hypotheses `1 ≤ n`, `2 ≤ d`,
`Even d` restore the classical statement. Both readings of "degree d" (`totalDegree = d` and
`totalDegree ≤ d`) are stated as a conjunction. The nonnegative polynomials of degree at most `d`
are the published cone `NieYangPareto.nonnegCone K d` with `K = ℝⁿ` (`Set.univ`). -/
theorem theorem_1_1 (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d) (hev : Even d) :
    (SigmaPoly n d = NPoly n d ↔ (n = 1 ∨ d = 2 ∨ (n = 2 ∧ d = 4))) ∧
    (SigmaPolyLe n d = NieYangPareto.nonnegCone (Set.univ : Set (Fin n → ℝ)) d ↔
      (n = 1 ∨ d = 2 ∨ (n = 2 ∧ d = 4))) := by sorry

end SPQPoly
