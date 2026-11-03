-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_matching_dominated_of_bipartite
-- name    : QuantumMaxCutEnergy.matching_dominated_of_bipartite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T04:38:35.980944+00:00
-- url     : https://prove2.me/theorems/2c56630f-1ffe-4f0a-8ad7-f7404e91c913
-- title:
--   Bipartite case of Edmonds' exactness: a load-polytope point is dominated by an integral matching
-- statement:
--   **The bipartite case of Edmonds' exactness of the matching polytope.**
--
--   Let $x\ge0$ be a weight on the edges of a graph on $n$ vertices, with vertex loads
--   $\mathrm{load}_x(v)=\sum_{e\ni v}x_e\le1$ everywhere, and suppose the *support* of $x$ is bipartite: there is a
--   colouring $c$ of the vertices such that every edge $e$ with $x_e\neq0$ has $c(e_1)\neq c(e_2)$. Then, for any
--   edge weights $w$, there is an integral matching $M$ with
--   $$\sum_{e}w_e\,x_e\ \le\ \sum_{e\in M}w_e .$$
--   That is: over a bipartite support, a point of the fractional matching polytope (described by the vertex-load
--   constraints alone — the odd-set constraints are automatic there) is dominated by an integral matching.
--
--   **Proof.** Pad $x$ to the symmetric matrix $\mathrm{padWeight}\,x$ with the deficits $1-\mathrm{load}_x(v)$ on the
--   diagonal; it is doubly stochastic, so by Birkhoff–von Neumann
--   $\mathrm{padWeight}\,x=\sum_\sigma\lambda_\sigma P_\sigma$ with $\lambda_\sigma\ge0$ and $\sum_\sigma\lambda_\sigma=1$.
--   The double-counting identity turns the objective into a weighted average of permutation step sums,
--   $$2\sum_ew_ex_e=\sum_\sigma\lambda_\sigma\sum_aw_{\{a,\sigma a\}},$$
--   and any $\sigma$ with $\lambda_\sigma\neq0$ has $\lambda_\sigma>0$, hence its nontrivial steps are nonzero
--   entries of $\mathrm{padWeight}\,x$, hence nonzero pair weights, so the previous node bounds
--   $\sum_aw_{\{a,\sigma a\}}\le2\sum_{e\in M_\sigma}w_e$ for some matching $M_\sigma$. Choosing $\sigma$ whose
--   matching is heaviest gives $2\sum_ew_ex_e\le2\sum_{e\in M}w_e$.
--
--   **Role.** This closes the bipartite half of `QuantumMaxCutEnergy.matching_polytope_integral_rounding`, the
--   missing piece of the matching state of the $0.595$ quantum max-cut analysis. The general (non-bipartite) case
--   needs the odd-set constraints to eliminate odd cycles, but over a bipartite support the padding argument
--   suffices.
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Birkhoff-von Neumann; Lee-Parekh arXiv:2401.03616 Section 2.3 (the matching state of the 0.595 analysis).

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Bipartite case of Edmonds' exactness**: a nonnegative edge weight whose vertex loads are at most `1` and
whose support is bipartite is dominated by an integral matching. -/
theorem matching_dominated_of_bipartite {n : ℕ} (w x : Edge n → ℝ) (c : Fin n → Bool)
    (hx : ∀ e, 0 ≤ x e) (hload : ∀ v, loadAt x v ≤ 1)
    (hc : ∀ e : Edge n, x e ≠ 0 → c e.val.1 ≠ c e.val.2) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      ∑ e, w e * x e ≤ ∑ e ∈ M, w e := by sorry

end QuantumMaxCutEnergy
