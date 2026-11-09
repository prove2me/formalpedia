-- Prove2me | Theorems.Thm_TZLevelsADO_lemma_3
-- name    : TZLevelsADO.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:50:39.27255+00:00
-- url     : https://prove2.me/theorems/5b75cd53-495a-4dcc-acdc-1f89656ed134
-- title:
--   Lemma 3 — large one-level growth puts both cross pivots in the bunches
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$.
--
--   Let $x, v$ be vertices and $1 \le j \le k-1$. If
--   $$h_j(v) - h_{j-1}(v) > 2d(x, v),$$
--   then $p_{j-1}(x) \in B(v)$ and $p_{j-1}(v) \in B(x)$.
--
--   So if the one-level growth of a vertex exceeds twice its distance to another vertex, each of the two has a pivot in the bunch of the other. This is used for the short part of the path in the Long–Short Growth Lemma.
--
--   Differences from the source:
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Lemma 3, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_TZLevelsADO_Hierarchy

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Lemma 3, p.7 (PDF p.8):
"Let x, v ∈ V and 1 ≤ j ≤ k − 1. If h_j(v) − h_{j−1}(v) > 2d(x, v), then p_{j−1}(x) ∈ B(v) and
p_{j−1}(v) ∈ B(x)."

**Formalization Note.** Stated for every admissible hierarchy `A` and every pivot choice `P`, on every
connected edge-list (multi)graph with positive real weights. `P.h j v = d(v, p_j(v))`. -/
theorem lemma_3 {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (x v : Fin G.n) (j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k - 1)
    (h : P.h j v - P.h (j - 1) v > 2 * dist G x v) :
    P.p (j - 1) x ∈ bunch A v ∧ P.p (j - 1) v ∈ bunch A x := by sorry

end TZLevelsADO
