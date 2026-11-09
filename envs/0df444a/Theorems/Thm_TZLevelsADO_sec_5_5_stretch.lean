-- Prove2me | Theorems.Thm_TZLevelsADO_sec_5_5_stretch
-- name    : TZLevelsADO.sec_5_5_stretch
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:52:05.005222+00:00
-- url     : https://prove2.me/theorems/00ac4aa5-f401-4fb8-81ce-545f590a1b2e
-- title:
--   §5.5 — Algorithm 2 has stretch $\frac65 k + 7$
-- statement:
--   Throughout, $G$ is a connected undirected graph on $n$ vertices with $m$ edges and positive real edge weights $\ell$, $d$ is its shortest-path distance, $V = A_0 \supseteq A_1 \supseteq \cdots \supseteq A_k = \emptyset$ is a Thorup–Zwick hierarchy with $A_{k-1} \neq \emptyset$, $p_i(u)$ is a closest vertex of $A_i$ to $u$, $h_i(u) = d(u, p_i(u))$, and $B(u)$ is the bunch of $u$. Let $\hat d(u, v)$ be the estimate of Algorithm 2.
--
--   For all vertices $u, v$,
--   $$d(u, v) \le \hat d(u, v) \le \Big(\frac65 k + 7\Big)\, d(u, v).$$
--
--   This is the stretch analysis of Algorithm 2: the lower bound is §5.2, and the upper bound combines the last-level bound, the Two-Level and Long–Short Growth Lemmas and Lemma 11. It holds for every outcome of the sampling, and it is the stretch clause of Theorem 1.
--
--   Differences from the source:
--   - generalization: one sampled hierarchy V = A₀ ⊇ ⋯ ⊇ A_k = ∅ with a fixed vertex added to A₁, …, A_{k−1}, and one argmin choice of pivots → every nested family A with A₀ = V, A_{k−1} ≠ ∅, A_k = ∅, and every argmin pivot choice; reason: the stretch analysis holds "for every outcome of the sampling" (p.7) and uses only A_{k−1} ≠ ∅; the sampled hierarchy with any argmin choice is an instance
--   - generalization: an undirected graph G = (V, E) with positive real edge weights → an edge list on Fin n with positive real weights; parallel edges and loops allowed; reason: every weighted graph is an instance; a loop never shortens a walk and a parallel edge only adds walks
--   - encoding: G is connected → Connected G: n ≥ 1 and every two vertices are joined by a walk; reason: a connected graph has a vertex; no instance of the source is excluded
-- source:
--   Chechik, Kadria, Lifshitz, Roditty, Reading between the levels: new tools for the Thorup–Zwick hierarchy and their applications, arXiv:2611.01297 (held file sha256 dfeca900…), §5.5, p.23 (PDF p.24), with §5.2, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_TZLevelsADO_estimate

namespace TZLevelsADO

/-- S. Chechik, A. Kadria, G. Lifshitz, L. Roditty, *Reading between the levels*, arXiv:2611.01297
(held file sha256 dfeca900…), §5.5, p.23 (PDF p.24), the stretch of Algorithm 2:
"By the definitions of X_i, Y_i, x_i, and y_i, every feasible expression in this minimum gives, through
the corresponding bound above, an estimate of at most 2D times that expression plus 3D. Therefore,
d̂(u, v) ≤ 2D · Q + 3D ≤ (6/5 k + 7) D." Together with §5.2, p.18: "every estimate is the length of
some u–v walk, so d̂(u, v) ≥ d(u, v)."

**Formalization Note.** As everywhere in §5 this holds "for every outcome of the sampling" (p.7): it is
stated for every admissible hierarchy `A` and every pivot choice `P` (ties broken arbitrarily), on every
connected edge-list (multi)graph with positive real weights. The estimate is `estimate P u v`
(Algorithm 2, lines 3–10) in `WithTop ℝ`.
Both inequalities hold for every pair, `u = v` included. -/
theorem sec_5_5_stretch {G : Graph} (hw : G.PosWeights) (hc : G.Connected) {k : ℕ} (A : Hierarchy G k)
    (P : PivotChoice A) (u v : Fin G.n) :
    ((dist G u v : ℝ) : WithTop ℝ) ≤ estimate P u v ∧
      estimate P u v ≤ ((((6 / 5 : ℝ) * k + 7) * dist G u v : ℝ) : WithTop ℝ) := by sorry

end TZLevelsADO
