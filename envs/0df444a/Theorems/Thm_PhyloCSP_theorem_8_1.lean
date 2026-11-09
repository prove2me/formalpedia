-- Prove2me | Theorems.Thm_PhyloCSP_theorem_8_1
-- name    : PhyloCSP.theorem_8_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:22:11.600205+00:00
-- url     : https://prove2.me/theorems/13911702-99d1-4dad-8a4b-fd004c0ba4a2
-- title:
--   Theorem 8.1 — an exchangeability criterion
-- statement:
--   Let $X_1,X_2,\dots$ be real-valued random variables such that
--
--   1. all $X_i$ have the same distribution;
--   2. $(X_i,X_j)$ has the same distribution for every ordered pair $i\neq j$;
--   3. for every $n\ge1$ and $i\le n$ there is $j>n$ with
--   $$
--   (X_1,\dots,X_n)\overset d=(X_1,\dots,X_{i-1},X_j,X_{i+1},\dots,X_n).
--   $$
--
--   Then the sequence is exchangeable: its joint distribution is unchanged by every permutation of finitely many indices.
--
--   The criterion is the tool behind Corollary 8.2, the exchangeability of $\mathrm{Aut}(\mathcal F)$-invariant families.
--
--   Differences from the source:
--   - encoding: indices 1, 2, …; in (iii) i ≤ n and j > n → indices 0, 1, …; in (iii) i < n and j ≥ n; reason: 0-based indexing of the same sequence
--   - encoding: random variables and equality in distribution → measurable maps on a probability space; equality of push-forward measures on ℝ × ℝ, Fin n → ℝ and ℕ → ℝ (product σ-algebras); reason: standard measure-theoretic reading
-- source:
--   Makarychev, Approximation Algorithms for Satisfiable Phylogenetic CSPs, STOC 2027 submission (manuscript sha256 3444b6c029bce73ce9a6ad0ae6bc8386c291dcb0b1e504e8216c60cd4d682dac), Theorem 8.1, p.24 (PDF p.26)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace PhyloCSP

/-- Makarychev, *Approximation Algorithms for Satisfiable Phylogenetic CSPs*, STOC 2027
submission (manuscript sha256 3444b6c0…682dac), Theorem 8.1, p.24 (PDF p.26): "Let X1, X2, . . . be
real-valued random variables. Suppose that (i) all Xi have the same distribution; (ii) (Xi, Xj) has
the same distribution for every ordered pair i ≠ j; (iii) for every n ≥ 1 and i ≤ n, there is
j > n such that (X1, . . . , Xn) =ᵈ (X1, . . . , Xi−1, Xj, Xi+1, . . . , Xn). Then the sequence is
exchangeable." Exchangeable (p.24): "their joint distribution is unchanged by every permutation of
finitely many indices".

**Formalization Note.** Indices are 0-based: `X 0, X 1, …`; in (iii) `i < n` and `j ≥ n`
(the 1-based `i ≤ n`, `j > n`). Random variables are measurable maps on a probability space;
equalities of distributions are equalities of push-forward measures (on `ℝ × ℝ`, `Fin n → ℝ`,
`ℕ → ℝ` with the product σ-algebras). Exchangeability: for every permutation `σ` of `ℕ` moving
finitely many indices, `(X (σ i))ᵢ` has the law of `(X i)ᵢ`. -/
theorem theorem_8_1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (h1 : ∀ i j, P.map (X i) = P.map (X j))
    (h2 : ∀ i j i' j', i ≠ j → i' ≠ j' →
      P.map (fun ω => (X i ω, X j ω)) = P.map (fun ω => (X i' ω, X j' ω)))
    (h3 : ∀ n : ℕ, 1 ≤ n → ∀ i < n, ∃ j, n ≤ j ∧
      P.map (fun ω (t : Fin n) => X t ω) =
        P.map (fun ω (t : Fin n) => X (if (t : ℕ) = i then j else t) ω)) :
    ∀ σ : Equiv.Perm ℕ, {i | σ i ≠ i}.Finite →
      P.map (fun ω i => X (σ i) ω) = P.map (fun ω i => X i ω) := by sorry

end PhyloCSP
