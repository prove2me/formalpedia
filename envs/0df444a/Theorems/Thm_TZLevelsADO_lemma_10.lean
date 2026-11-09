-- Prove2me | Theorems.Thm_TZLevelsADO_lemma_10
-- name    : TZLevelsADO.lemma_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:09.863205+00:00
-- url     : https://prove2.me/theorems/b1b49b9f-422d-41da-8e2b-793ffb2b1df6
-- title:
--   Lemma 10 (Long–Short Growth Lemma)
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$. Let $\hat d(u, v)$ be the estimate of Algorithm 2, $D = d(u, v)$, $\nabla_i(x) = h_i(x) - h_{i-2}(x)$ and $\Delta_j(x) = h_j(x) - h_{j-1}(x)$.
--
--   If for some $2 \le i < k$ and $1 \le j < k$
--   $$\nabla_i(u) + \Delta_j(v) > 2D,$$
--   then
--   $$\hat d(u, v) \le 2h_{i-1}(u) + 2h_{j-1}(v) + 3D.$$
--   The same holds with $u$ and $v$ exchanged: if $\nabla_i(v) + \Delta_j(u) > 2D$, then $\hat d(u, v) \le 2h_{i-1}(v) + 2h_{j-1}(u) + 3D$.
--
--   A large two-level growth at one endpoint combined with a large one-level growth at the other gives a short estimate. This is bound 3 of the optimization in §5.5.
--
--   Differences from the source:
--   - reading: "The same holds with u and v exchanged" (Lemma 10) → a second conjunct with the hypothesis and the bound exchanged in u and v, about the same estimate d̂(u, v); reason: this is how §5.5 item 3 uses it for the fixed pair ⟨u, v⟩; d̂ is symmetric (H is symmetric and d is symmetric), so it is also the literal exchange
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Lemma 10, p.21 (PDF p.22)

import Mathlib
import Definitions.Def_TZLevelsADO_estimate

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Lemma 10 (Long–Short Growth Lemma), p.21 (PDF p.22):
"If for some 2 ≤ i < k and 1 ≤ j < k, ∇_i(u) + ∆_j(v) > 2D, then
d̂(u, v) ≤ 2h_{i−1}(u) + 2h_{j−1}(v) + 3D. The same holds with u and v exchanged." Here D = d(u, v)
(§5.2, p.19).

**Formalization Note.** As everywhere in §5 this holds "for every outcome of the sampling" (p.7): it is
stated for every admissible hierarchy `A` and every pivot choice `P` (ties broken arbitrarily), on every
connected edge-list (multi)graph with positive real weights. The estimate is `estimate P u v`
(Algorithm 2, lines 3–10) in `WithTop ℝ`.
`P.twoLevel i u = ∇_i(u)`, `P.oneLevel j v = ∆_j(v)`. The second conjunct is "the same with u and v
exchanged" for the fixed pair ⟨u, v⟩, as it is used in §5.5 item 3 (p.23): hypothesis and bound
exchange `u` and `v`, the estimate stays `d̂(u, v)`. -/
theorem lemma_10 {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) (i j : ℕ) (hi2 : 2 ≤ i) (hik : i < k)
    (hj1 : 1 ≤ j) (hjk : j < k) :
    (P.twoLevel i u + P.oneLevel j v > 2 * dist G u v →
      estimate P u v ≤
        (((2 * P.h (i - 1) u + 2 * P.h (j - 1) v + 3 * dist G u v : ℝ)) : WithTop ℝ)) ∧
    (P.twoLevel i v + P.oneLevel j u > 2 * dist G u v →
      estimate P u v ≤
        (((2 * P.h (i - 1) v + 2 * P.h (j - 1) u + 3 * dist G u v : ℝ)) : WithTop ℝ)) := by sorry

end TZLevelsADO
