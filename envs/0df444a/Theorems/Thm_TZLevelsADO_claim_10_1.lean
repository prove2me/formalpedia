-- Prove2me | Theorems.Thm_TZLevelsADO_claim_10_1
-- name    : TZLevelsADO.claim_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:50:19.75339+00:00
-- url     : https://prove2.me/theorems/43cd9d21-7cc6-49d0-ba56-2923e22bd0ea
-- title:
--   Claim 10.1 (Long–Short Growth Lemma Part 1) — a splitting edge
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$. Let $u, v$ be vertices with $D = d(u, v)$, and let $\nabla_i(u) = h_i(u) - h_{i-2}(u)$ and $\Delta_j(v) = h_j(v) - h_{j-1}(v)$. Suppose that for some $2 \le i < k$ and $1 \le j < k$,
--   $$\nabla_i(u) + \Delta_j(v) > 2D \qquad\text{and}\qquad \nabla_i(u),\ \Delta_j(v) \le 2D.$$
--   Then for every shortest path $P$ from $u$ to $v$ there is an edge $(x, y)$ of $P$, oriented so that $u, x, y, v$ appear in this order, such that
--   $$\nabla_i(u) > 2d(u, x) \qquad\text{and}\qquad \Delta_j(v) > 2d(y, v).$$
--
--   The split point of the path may fall inside a heavy edge; the claim splits across that edge instead, which is what the weighted preprocessing of Algorithm 2 exploits.
--
--   Differences from the source:
--   - generalization: the fixed shortest path P = P(u, v) → every shortest walk W from u to v; reason: the page fixes an arbitrary one; with positive weights every shortest walk is a shortest path
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Claim 10.1, pp.21–22 (PDF pp.22–23)

import Mathlib
import Definitions.Def_TZLevelsADO_Hierarchy

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Claim 10.1 (Long–Short Growth Lemma Part 1), pp.21–22 (PDF pp.22–23):
"If for some 2 ≤ i < k and 1 ≤ j < k, ∇_i(u) + ∆_j(v) > 2D and ∇_i(u), ∆_j(v) ≤ 2D, then there exists
an edge (x, y) of P, oriented so that u, x, y, v appear in this order, such that ∇_i(u) > 2d(u, x) and
∆_j(v) > 2d(y, v)." Here P = P(u, v) and D = d(u, v) (§5.2, p.19).

**Formalization Note.**
* `P` is **every** shortest walk `W` from `u` to `v` (the page fixes one). An edge `(x, y)` of `W` with
  `u, x, y, v` in this order is a decomposition `W = W₁ ++ s :: W₂` with `x = tail s`, `y = head s`.
* `P.twoLevel i u = ∇_i(u)` and `P.oneLevel j v = ∆_j(v)`.
* Stated for every admissible hierarchy `A` and every pivot choice `P`, on every connected edge-list
  (multi)graph with positive real weights. -/
theorem claim_10_1 {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) (i j : ℕ) (hi2 : 2 ≤ i) (hik : i < k)
    (hj1 : 1 ≤ j) (hjk : j < k)
    (h : P.twoLevel i u + P.oneLevel j v > 2 * dist G u v)
    (hi : P.twoLevel i u ≤ 2 * dist G u v) (hj : P.oneLevel j v ≤ 2 * dist G u v)
    (W : List (Fin G.m × Bool)) (hW : IsShortestWalk G u v W) :
    ∃ W₁ s W₂, W = W₁ ++ s :: W₂ ∧
      P.twoLevel i u > 2 * dist G u (G.tail s) ∧ P.oneLevel j v > 2 * dist G (G.head s) v := by sorry

end TZLevelsADO
