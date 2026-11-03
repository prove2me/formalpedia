-- Prove2me | Theorems.Thm_QuantumMaxCutEnergy_exists_matching_ge_perm_sum_support
-- name    : QuantumMaxCutEnergy.exists_matching_ge_perm_sum_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T04:38:36.572967+00:00
-- url     : https://prove2.me/theorems/d5323cac-a81c-43d2-beea-9f023d11e66d
-- title:
--   A permutation with bipartite steps is dominated by twice an integral matching
-- statement:
--   **Per-permutation matching bound for a bipartite support.**
--
--   Let $x\ge0$ be an edge weight whose support is bipartite with colouring $c:V\to\{\text{false},\text{true}\}$
--   (every edge of the support joins two different colours), and let $\sigma$ be a permutation of the vertex set
--   all of whose nontrivial steps have *nonzero* pair weight: $x_{\{a,\sigma a\}}\neq0$ whenever $\sigma a\neq a$.
--   Then there is an integral matching $M$ with
--   $$\sum_{a}x_{\{a,\sigma a\}}\ \le\ 2\sum_{e\in M}w_e .$$
--
--   **Proof.** Split the sum over $a$ by the colour of $a$. Inside one colour class the edges $\{a,\sigma a\}$ are
--   pairwise disjoint: two of them sharing a vertex $v$ would have to share it as a vertex of the class (forcing
--   $a=a'$) or as a $\sigma$-image (forcing $\sigma a=\sigma a'$, hence $a=a'$ by injectivity), and a mixed
--   coincidence is impossible because the colours differ. So each colour class contributes at most the weight of a
--   matching, and the total is at most twice the better of the two.
--
--   **Role.** This is the combinatorial core of the bipartite case of Edmonds' exactness, and it replaces the
--   "decompose into even cycles, take alternating matchings" argument by a colour split that needs no cycle
--   machinery. Combined with Birkhoff's decomposition of the padded fractional matching it yields an integral
--   matching of weight at least the whole fractional weight
--   (`QuantumMaxCutEnergy.matching_dominated_of_bipartite`).
-- source:
--   Edmonds, J. Res. Nat. Bur. Standards 69B (1965); Birkhoff-von Neumann decomposition; the colour-split replaces the even-cycle decomposition in the bipartite case.

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Mathlib
open scoped BigOperators

namespace QuantumMaxCutEnergy

/-- **Per-permutation matching bound** (bipartite support): the steps of a permutation whose endpoints have
different colours carry at most twice the weight of a single integral matching. -/
theorem exists_matching_ge_perm_sum_support {n : ℕ} (w x : Edge n → ℝ)
    (c : Fin n → Bool) (hc : ∀ e : Edge n, x e ≠ 0 → c e.val.1 ≠ c e.val.2)
    (σ : Equiv.Perm (Fin n)) (hne : ∀ a, σ a ≠ a → pairWeight x a (σ a) ≠ 0) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      ∑ a, pairWeight w a (σ a) ≤ 2 * ∑ e ∈ M, w e := by sorry

end QuantumMaxCutEnergy
