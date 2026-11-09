-- Prove2me | Theorems.Thm_TZLevelsADO_claim_10_2
-- name    : TZLevelsADO.claim_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:33.452931+00:00
-- url     : https://prove2.me/theorems/50aa9cc2-5736-49b7-9396-126b07c787c3
-- title:
--   Claim 10.2 (Long–Short Growth Lemma Part 2)
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$. Let $\hat d(u, v)$ be the estimate of Algorithm 2, $D = d(u, v)$, $\nabla_i(u) = h_i(u) - h_{i-2}(u)$ and $\Delta_j(v) = h_j(v) - h_{j-1}(v)$.
--
--   Let $(x, y)$ be an edge of a shortest path from $u$ to $v$, oriented so that $u, x, y, v$ appear in this order. Suppose that there are $2 \le i < k$ and $1 \le j < k$ such that
--   $$\nabla_i(u) > 2d(u, x) \qquad\text{and}\qquad \Delta_j(v) > 2d(y, v).$$
--   Then
--   $$\hat d(u, v) \le 2h_{i-1}(u) + 2h_{j-1}(v) + 3D.$$
--
--   The long part of the path is covered through a pivot of $u$ or of $x$, and the short part adapts to whichever case holds, using the table entry stored for one of the two orientations of $(x, y)$.
--
--   Differences from the source:
--   - generalization: the fixed shortest path P = P(u, v) → every shortest walk W from u to v; reason: the page fixes an arbitrary one; with positive weights every shortest walk is a shortest path
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Claim 10.2, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_TZLevelsADO_estimate

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Claim 10.2 (Long–Short Growth Lemma Part 2), p.22 (PDF p.23):
"Let (x, y) be an edge of P(u, v), oriented so that u, x, y, v appear in this order. Suppose that there
are 2 ≤ i < k and 1 ≤ j < k such that ∇_i(u) > 2d(u, x) and ∆_j(v) > 2d(y, v). Then
d̂(u, v) ≤ 2h_{i−1}(u) + 2h_{j−1}(v) + 3D." Here D = d(u, v) (§5.2, p.19).

**Formalization Note.** As everywhere in §5 this holds "for every outcome of the sampling" (p.7): it is
stated for every admissible hierarchy `A` and every pivot choice `P` (ties broken arbitrarily), on every
connected edge-list (multi)graph with positive real weights. The estimate is `estimate P u v`
(Algorithm 2, lines 3–10) in `WithTop ℝ`.
`P(u, v)` is **any** shortest walk `W` from `u` to `v`; the edge is a decomposition
`W = W₁ ++ s :: W₂` with `x = tail s` and `y = head s`. -/
theorem claim_10_2 {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) (i j : ℕ) (hi2 : 2 ≤ i) (hik : i < k)
    (hj1 : 1 ≤ j) (hjk : j < k)
    (W : List (Fin G.m × Bool)) (hW : IsShortestWalk G u v W)
    (W₁ W₂ : List (Fin G.m × Bool)) (s : Fin G.m × Bool) (hsplit : W = W₁ ++ s :: W₂)
    (hx : P.twoLevel i u > 2 * dist G u (G.tail s))
    (hy : P.oneLevel j v > 2 * dist G (G.head s) v) :
    estimate P u v ≤
      (((2 * P.h (i - 1) u + 2 * P.h (j - 1) v + 3 * dist G u v : ℝ)) : WithTop ℝ) := by sorry

end TZLevelsADO
