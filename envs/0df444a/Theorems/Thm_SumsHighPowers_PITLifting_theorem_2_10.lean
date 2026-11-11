-- Prove2me | Theorems.Thm_SumsHighPowers_PITLifting_theorem_2_10
-- name    : SumsHighPowers.PITLifting.theorem_2_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:10:56.490374+00:00
-- url     : https://prove2.me/theorems/6bd98d7a-12c3-45c3-906d-3c2b07f3dcdb
-- title:
--   Theorem 2.10 — $d$-th powers of $r\ge3$ pairwise non-associate polynomials are linearly independent when $(r-1)^2\le d+1$
-- statement:
--   Let $r,d,\delta\in\mathbb N$ with $r\ge 3$, and let $F$ be a field of characteristic $p=0$ or $p>(r-1)d\delta$. Let $f_1,\dots,f_r\in F[x]$ be pairwise non-associate polynomials (pairwise linearly independent over $F$) of degree at most $\delta$. If
--   $$(r-1)^2\le d+1,$$
--   then $f_1^{\,d},\dots,f_r^{\,d}$ are linearly independent over $F$.
--
--   This is the statement that a short sum of high powers of pairwise non-associate univariate polynomials cannot vanish; it is what the PIT lifting theorem (Theorem 3.1) applies after restricting to a curve.
--
--   **Formalization Note.** The family is `f : Fin r → F[X]`; pairwise non-associate is the mission's `PairwiseNonAssociate` (pairwise linear independence, p. 12).
--
--   Differences from the source:
--   - reading: f_1, …, f_r pairwise non-associate (associate: g = αf for nonzero f, g and nonzero α) → `PairwiseNonAssociate`: any two members with distinct indices are linearly independent over F; reason: the paper states on p. 12 that non-associate is equivalent to pairwise linearly independent; the reading also makes every member nonzero, without which the statement would fail (a zero member)
--   - encoding: f_1, …, f_r of degree at most δ; f_1^d, …, f_r^d linearly independent → `f : Fin r → F[X]`, `∀ i, (f i).natDegree ≤ δ`; `LinearIndependent F (fun i => f i ^ d)`; reason: relabelling; every f_i is nonzero (r ≥ 3), where natDegree is deg
--   - encoding: F of characteristic p with p = 0 or p > (r − 1)dδ → `ringChar F = 0 ∨ (r - 1) * d * δ < ringChar F`; reason: the characteristic of a field is 0 or a prime p, and `ringChar F` is that number
-- source:
--   Kaplan, Shpilka, Tal, PIT and Reconstruction for Sums of High Powers, STOC 2027 submission (manuscript, sha256 63d31ceb…9b604b19), p. 20, Theorem 2.10 ([VW03, Corollary 3.8])

import Mathlib
import Definitions.Def_SumsHighPowers_PITLifting_PairwiseNonAssociate

namespace SumsHighPowers.PITLifting

/-- **Theorem 2.10** ([VW03, Corollary 3.8]; Kaplan–Shpilka–Tal, p. 20). Let `r, d, δ ∈ ℕ`, `r ≥ 3`,
and let `F` have characteristic `p = 0` or `p > (r − 1)dδ`. Let `f₁, …, f_r ∈ F[x]` be pairwise
non-associate polynomials of degree at most `δ`. If `(r − 1)² ≤ d + 1` then `f₁^d, …, f_r^d` are
linearly independent. -/
theorem theorem_2_10 {F : Type*} [Field F] (r d δ : ℕ) (hr : 3 ≤ r)
    (hchar : ringChar F = 0 ∨ (r - 1) * d * δ < ringChar F)
    (f : Fin r → Polynomial F) (hna : PairwiseNonAssociate (F := F) f)
    (hdeg : ∀ i, (f i).natDegree ≤ δ)
    (hrd : (r - 1) ^ 2 ≤ d + 1) :
    LinearIndependent F (fun i => f i ^ d) := by sorry

end SumsHighPowers.PITLifting
