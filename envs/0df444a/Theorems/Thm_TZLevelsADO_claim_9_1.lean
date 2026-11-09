-- Prove2me | Theorems.Thm_TZLevelsADO_claim_9_1
-- name    : TZLevelsADO.claim_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:50:09.137203+00:00
-- url     : https://prove2.me/theorems/ff5368e6-26ca-446a-8aaa-baa44d8a14b3
-- title:
--   Claim 9.1 — a crossing edge for the Two-Level Growth Lemma
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$. Let $u, v$ be vertices with $D = d(u, v)$ and let $2 \le i < k$. Assume
--   $$h_i(u) - h_{i-2}(v) > D, \qquad h_{i-1}(v) > h_{i-2}(v), \qquad h_{i-1}(u) \le h_{i-2}(v) + D.$$
--   Then for every shortest path $P$ from $u$ to $v$ there is an edge $(x, y)$ of $P$, oriented from $u$ to $v$, such that
--   $$h_i(u) - h_{i-1}(x) > d(u, x) \qquad\text{and}\qquad h_{i-1}(y) - h_{i-2}(v) > d(y, v).$$
--
--   The three assumptions are the hypothesis of Lemma 9 and the two assumptions in force after its easy cases. The edge is where Algorithm 2's table connects a pivot of $x$ with a pivot of $v$.
--
--   Differences from the source:
--   - reading: the claim inside the proof of Lemma 9, under the assumptions in force there → the hypotheses h_i(u) − h_{i−2}(v) > D, h_{i−1}(v) > h_{i−2}(v), h_{i−1}(u) ≤ h_{i−2}(v) + D stated explicitly; reason: these are Lemma 9's hypothesis and the "We may therefore assume" line of p.20, the only assumptions the claim's proof uses
--   - generalization: the fixed shortest path P = P(u, v) → every shortest walk W from u to v; reason: the page fixes an arbitrary one; with positive weights every shortest walk is a shortest path
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), Claim 9.1, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_TZLevelsADO_Hierarchy

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), Claim 9.1, p.20 (PDF p.21), inside the proof of Lemma 9:
"There exists an edge (x, y) of P(u, v), oriented from u to v, such that
h_i(u) − h_{i−1}(x) > d(u, x) and h_{i−1}(y) − h_{i−2}(v) > d(y, v)."

The hypotheses are those in force at that point of the proof: Lemma 9's "for some 2 ≤ i < k,
h_i(u) − h_{i−2}(v) > D", and "We may therefore assume that h_{i−1}(v) > h_{i−2}(v) and
h_{i−1}(u) ≤ h_{i−2}(v) + D." (p.20), with D = d(u, v).

**Formalization Note.**
* `P(u, v)` is **every** shortest walk `W` from `u` to `v` (the page fixes one). An edge of `W`
  oriented from `u` to `v` is a decomposition `W = W₁ ++ s :: W₂`: the oriented edge `s` runs from
  `x = tail s` to `y = head s`, and `W₁` leads from `u` to `x`.
* Stated for every admissible hierarchy `A` and every pivot choice `P`, on every connected edge-list
  (multi)graph with positive real weights. -/
theorem claim_9_1 {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) (i : ℕ) (hi2 : 2 ≤ i) (hik : i < k)
    (h1 : P.h i u - P.h (i - 2) v > dist G u v)
    (h2 : P.h (i - 1) v > P.h (i - 2) v)
    (h3 : P.h (i - 1) u ≤ P.h (i - 2) v + dist G u v)
    (W : List (Fin G.m × Bool)) (hW : IsShortestWalk G u v W) :
    ∃ W₁ s W₂, W = W₁ ++ s :: W₂ ∧
      P.h i u - P.h (i - 1) (G.tail s) > dist G u (G.tail s) ∧
      P.h (i - 1) (G.head s) - P.h (i - 2) v > dist G (G.head s) v := by sorry

end TZLevelsADO
