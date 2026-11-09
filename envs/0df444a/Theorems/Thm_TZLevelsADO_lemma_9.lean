-- Prove2me | Theorems.Thm_TZLevelsADO_lemma_9
-- name    : TZLevelsADO.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:17.369208+00:00
-- url     : https://prove2.me/theorems/d63c4ef0-5dc3-4567-ae14-eaba41e3cb0a
-- title:
--   Lemma 9 (Two-Level Growth Lemma)
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$. Let $\hat d(u, v)$ be the estimate of Algorithm 2 and $D = d(u, v)$.
--
--   If for some $2 \le i < k$
--   $$h_i(u) - h_{i-2}(v) > D,$$
--   then
--   $$\hat d(u, v) \le 2h_{i-2}(v) + h_{i-1}(u) + h_i(u) + D.$$
--   The same holds with $u$ and $v$ exchanged: if $h_i(v) - h_{i-2}(u) > D$, then $\hat d(u, v) \le 2h_{i-2}(u) + h_{i-1}(v) + h_i(v) + D$.
--
--   The intermediate level $i-1$ connects level $i$ at one endpoint to level $i-2$ at the other. This is bound 2 of the optimization in §5.5.
--
--   Differences from the source:
--   - reading: "The same holds with u and v exchanged" (Lemma 9) → a second conjunct with the hypothesis and the bound exchanged in u and v, about the same estimate d̂(u, v); reason: this is how §5.5 item 2 uses it for the fixed pair ⟨u, v⟩; d̂ is symmetric (H is symmetric and d is symmetric), so it is also the literal exchange
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Lemma 9, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_TZLevelsADO_estimate

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Lemma 9 (Two-Level Growth Lemma), p.19 (PDF p.20):
"If for some 2 ≤ i < k, h_i(u) − h_{i−2}(v) > D, then d̂(u, v) ≤ 2h_{i−2}(v) + h_{i−1}(u) + h_i(u) + D.
The same holds with u and v exchanged." Here D = d(u, v) (§5.2, p.19).

**Formalization Note.** As everywhere in §5 this holds "for every outcome of the sampling" (p.7): it is
stated for every admissible hierarchy `A` and every pivot choice `P` (ties broken arbitrarily), on every
connected edge-list (multi)graph with positive real weights. The estimate is `estimate P u v`
(Algorithm 2, lines 3–10) in `WithTop ℝ`.
The second conjunct is "the same with u and v exchanged" for the fixed pair ⟨u, v⟩, as it is used in
§5.5 item 2 (p.23): the hypothesis and the bound exchange `u` and `v`, the estimate stays `d̂(u, v)`.
(Exchanging `u` and `v` in the first conjunct as well only gives an instance of the first conjunct.) -/
theorem lemma_9 {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) (i : ℕ) (hi2 : 2 ≤ i) (hik : i < k) :
    (P.h i u - P.h (i - 2) v > dist G u v →
      estimate P u v ≤
        (((2 * P.h (i - 2) v + P.h (i - 1) u + P.h i u + dist G u v : ℝ)) : WithTop ℝ)) ∧
    (P.h i v - P.h (i - 2) u > dist G u v →
      estimate P u v ≤
        (((2 * P.h (i - 2) u + P.h (i - 1) v + P.h i v + dist G u v : ℝ)) : WithTop ℝ)) := by sorry

end TZLevelsADO
