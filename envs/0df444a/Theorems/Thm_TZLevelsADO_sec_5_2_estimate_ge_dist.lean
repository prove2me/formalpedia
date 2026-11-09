-- Prove2me | Theorems.Thm_TZLevelsADO_sec_5_2_estimate_ge_dist
-- name    : TZLevelsADO.sec_5_2_estimate_ge_dist
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:51:26.69553+00:00
-- url     : https://prove2.me/theorems/6e2b50fe-7c45-4e13-b1d4-c622ae9d0c93
-- title:
--   §5.2 — every estimate is a walk length, $\hat d(u,v) \ge d(u,v)$
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$. Let $\hat d(u, v)$ be the estimate of Algorithm 2.
--
--   For all vertices $u, v$,
--   $$d(u, v) \le \hat d(u, v).$$
--
--   Every value the query considers is the length of some walk from $u$ to $v$, so the oracle never underestimates; this is the lower half of the stretch guarantee.
--
--   Differences from the source:
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §5.2, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_TZLevelsADO_estimate

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), §5.2, p.18 (PDF p.19):
"The query may find other walks as well, but every estimate is the length of some u–v walk, so
d̂(u, v) ≥ d(u, v)."

**Formalization Note.** As everywhere in §5 this holds "for every outcome of the sampling" (p.7): it is
stated for every admissible hierarchy `A` and every pivot choice `P` (ties broken arbitrarily), on every
connected edge-list (multi)graph with positive real weights. The estimate is `estimate P u v`
(Algorithm 2, lines 3–10) in `WithTop ℝ`. -/
theorem sec_5_2_estimate_ge_dist {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) :
    ((dist G u v : ℝ) : WithTop ℝ) ≤ estimate P u v := by sorry

end TZLevelsADO
