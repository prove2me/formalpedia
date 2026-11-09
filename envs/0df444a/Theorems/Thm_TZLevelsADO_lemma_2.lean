-- Prove2me | Theorems.Thm_TZLevelsADO_lemma_2
-- name    : TZLevelsADO.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:50:38.852324+00:00
-- url     : https://prove2.me/theorems/9489aeb9-db17-47e9-b0c3-5b4e40c82ec2
-- title:
--   Lemma 2 ([TZ05]) — the previous-level pivot of $v$ lies in $B(u)$
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$.
--
--   Let $u, v$ be vertices and $1 \le i \le k-1$. If
--   $$d(u, v) + h_{i-1}(v) < h_i(u),$$
--   then $p_{i-1}(v) \in B(u)$, and
--   $$d(u, p_{i-1}(v)) + d(p_{i-1}(v), v) \le 2h_i(u) - d(u, v).$$
--
--   This is the basic Thorup–Zwick step: when the level-$i$ ball around $u$ is large compared with $d(u,v)$, a pivot of $v$ is already in the bunch of $u$, which gives a short estimate. It is used in every case analysis of the mission.
--
--   Differences from the source:
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Lemma 2, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_TZLevelsADO_Hierarchy

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Lemma 2 ([TZ05]), p.7 (PDF p.8):
"Let u, v ∈ V and 1 ≤ i ≤ k − 1. If d(u, v) + h_{i−1}(v) < h_i(u), then p_{i−1}(v) ∈ B(u), and
d(u, p_{i−1}(v)) + d(p_{i−1}(v), v) ≤ 2h_i(u) − d(u, v)."

**Formalization Note.** Stated for every admissible hierarchy `A` and every pivot choice `P` (the page
fixes one sampled hierarchy and one argmin choice; its proof uses neither), on every connected
edge-list (multi)graph with positive real weights. `P.h i u = d(u, p_i(u))`. -/
theorem lemma_2 {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) (i : ℕ) (hi1 : 1 ≤ i) (hik : i ≤ k - 1)
    (h : dist G u v + P.h (i - 1) v < P.h i u) :
    P.p (i - 1) v ∈ bunch A u ∧
      dist G u (P.p (i - 1) v) + dist G (P.p (i - 1) v) v ≤ 2 * P.h i u - dist G u v := by sorry

end TZLevelsADO
