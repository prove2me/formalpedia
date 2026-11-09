-- Prove2me | Theorems.Thm_TZLevelsADO_sec_5_5_last_level_bound
-- name    : TZLevelsADO.sec_5_5_last_level_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:26.519716+00:00
-- url     : https://prove2.me/theorems/4f660a68-79ce-4c26-974e-3f7b736f469b
-- title:
--   §5.5, bound 1 — the last-level bound $\hat d(u,v) \le 2\min(h_{k-1}(u),h_{k-1}(v)) + D$
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$. Let $\hat d(u, v)$ be the estimate of Algorithm 2 and $D = d(u, v)$.
--
--   For all vertices $u, v$,
--   $$\hat d(u, v) \le 2\min\big(h_{k-1}(u), h_{k-1}(v)\big) + D.$$
--
--   This is the first of the three bounds combined in §5.5: since $B_{k-1}(\cdot) = A_{k-1}$, the top-level pivot of either endpoint is in the bunch of the other.
--
--   Differences from the source:
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §5.5, item 1, p.23 (PDF p.24)

import Mathlib
import Definitions.Def_TZLevelsADO_estimate

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), §5.5, item 1, p.23 (PDF p.24), for the pair ⟨u, v⟩ with
D = d(u, v) (§5.2, p.19: "fix a pair ⟨u, v⟩ of vertices, and let P = P(u, v) and D = d(u, v)"):
"d̂(u, v) ≤ 2 min(h_{k−1}(u), h_{k−1}(v)) + D."

**Formalization Note.** As everywhere in §5 this holds "for every outcome of the sampling" (p.7): it is
stated for every admissible hierarchy `A` and every pivot choice `P` (ties broken arbitrarily), on every
connected edge-list (multi)graph with positive real weights. The estimate is `estimate P u v`
(Algorithm 2, lines 3–10) in `WithTop ℝ`. -/
theorem sec_5_5_last_level_bound {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) :
    estimate P u v ≤
      (((2 * min (P.h (k - 1) u) (P.h (k - 1) v) + dist G u v : ℝ)) : WithTop ℝ) := by sorry

end TZLevelsADO
