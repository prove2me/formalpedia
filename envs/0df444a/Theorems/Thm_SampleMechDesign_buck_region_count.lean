-- Prove2me | Theorems.Thm_SampleMechDesign_buck_region_count
-- name    : SampleMechDesign.buck_region_count
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:11:32.549035+00:00
-- url     : https://prove2.me/theorems/979414d5-2552-4c67-9471-850e205e68dc
-- title:
--   Buck's region count, cited p.11 (corrected: Buck's bound $\sum_{i\le d}\binom mi$ in place of $d\,m^d$)
-- statement:
--   Let $H$ be a finite set of $m$ hyperplanes $\{p: a\cdot p=b\}$, $a\neq0$, in $\mathbb R^d$. Then the number of connected components of the complement of their union is at most
--
--   $$
--   \sum_{i=0}^{d}\binom{m}{i}.
--   $$
--
--   This is the region count of Buck (1943). The proof of Lemma 3.10 uses it to bound the number of pieces on which all the profit functions of a sample are simultaneously affine.
--
--   **Formalization Note** The count is the extended cardinality `ENat.card`, so an infinite set of components is not read as $0$. Two pairs in $H$ may describe one hyperplane, which only lowers the count.
--
--   Differences from the source:
--   - correction: τ < d(Nt)^d for Nt hyperplanes → at most the sum of C(m, i), i = 0..d, for m hyperplanes; reason: the printed bound is false: one point in ℝ¹ gives 2 regions and d·m^d = 1. The sum is the sharp bound of the cited theorem
--   - correction: components of P \ (union of the hyperplanes) → components of the complement in ℝ^d; reason: the cited theorem is about ℝ^d, and for non-convex P the printed count is unbounded (P = ℕ, correction of Definition 3.5)
--   - encoding: τ a number of regions → ENat.card of the connected components of the subtype; reason: extended cardinality reads an infinite count as ∞, never as 0
-- source:
--   Balcan, Sandholm, Vitercik, Generalization Guarantees for Multi-item Profit Maximization: Pricing, Auctions, and Randomized Mechanisms, arXiv:1705.00243v6, proof of Lemma 3.10, p.11 (PDF p.11), citing [18, Theorem 1]: R. C. Buck, Partition of space, Amer. Math. Monthly 50 (1943) 541–544

import Mathlib

namespace SampleMechDesign

/-- **Buck's region count (corrected).** R. C. Buck, *Partition of space*, Amer. Math. Monthly 50
(1943), Theorem 1, as cited in Balcan, Sandholm, Vitercik, arXiv:1705.00243v6, proof of Lemma 3.10,
p.11. A finite set `H` of hyperplanes `{p | a ⬝ᵥ p = b}`, `a ≠ 0`, in `ℝ^d` cuts `ℝ^d` into at most
`∑_{i ≤ d} C(|H|, i)` connected components.

**Formalization Note.** The paper's "τ < d(Nt)^d" is false: one point in `ℝ¹` gives `2` regions and
`d m^d = 1`. The count is `ENat.card`, so an infinite set of components is not read as `0`. Two
pairs of `H` may describe one hyperplane; that only lowers the count. -/
theorem buck_region_count {d : ℕ} (H : Finset ((Fin d → ℝ) × ℝ)) (hH : ∀ h ∈ H, h.1 ≠ 0) :
    ENat.card (ConnectedComponents ↥((⋃ h ∈ H, {p : Fin d → ℝ | h.1 ⬝ᵥ p = h.2})ᶜ)) ≤
      ((∑ i ∈ Finset.range (d + 1), H.card.choose i : ℕ) : ℕ∞) := by sorry

end SampleMechDesign
