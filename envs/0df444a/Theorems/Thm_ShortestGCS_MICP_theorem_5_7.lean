-- Prove2me | Theorems.Thm_ShortestGCS_MICP_theorem_5_7
-- name    : ShortestGCS.MICP.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:12:50.709362+00:00
-- url     : https://prove2.me/theorems/72609306-3f7e-481a-954f-cd2a76e3f94e
-- title:
--   Theorem 5.7, p. 10 — the MICP (5.5) has optimal value equal to the SPP in GCS (2.1)
-- statement:
--   Let $G = (\mathcal V, \mathcal E)$ be a finite directed graph with source $s$ and target $t \ne s$, where every vertex $v$ carries a nonempty compact convex set $\mathcal X_v \subseteq \mathbb R^n$ and every edge $e$ a nonnegative, proper, closed, convex length $\ell_e : \mathbb R^n\times\mathbb R^n \to \mathbb R_{\ge 0}\cup\{\infty\}$. Assume no edge enters $s$ and no edge leaves $t$. Then the optimal value of the mixed-integer convex program
--
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & \textstyle\sum_{e\in\mathcal E} \tilde\ell_e(z_e, z'_e, y_e)\\
--   \text{subject to}\quad & \textstyle\sum_{e\in\mathcal E^{\mathrm{out}}_s} y_e = 1,\ \sum_{e\in\mathcal E^{\mathrm{in}}_t} y_e = 1,\\
--   & \textstyle\sum_{e\in\mathcal E^{\mathrm{out}}_v} y_e \le 1, \quad \sum_{e\in\mathcal E^{\mathrm{in}}_v} (z'_e, y_e) = \sum_{e\in\mathcal E^{\mathrm{out}}_v} (z_e, y_e) \qquad \forall v \ne s,t,\\
--   & (z_e, y_e) \in \tilde{\mathcal X}_u,\ (z'_e, y_e) \in \tilde{\mathcal X}_v,\ y_e \in \{0,1\} \qquad \forall e = (u,v) \in \mathcal E
--   \end{aligned}
--   \tag{5.5}
--   $$
--
--   equals the optimal value of the shortest-path problem in the graph of convex sets
--
--   $$
--   \inf\Big\{\sum_{e=(u,v)\in\mathcal E_p} \ell_e(x_u, x_v) \;:\; p \text{ an } s\text{-}t \text{ path},\ x_v \in \mathcal X_v\ \forall v\in p\Big\}. \tag{2.1}
--   $$
--
--   Here $\tilde{\mathcal X}_v$ is the perspective cone of $\mathcal X_v$ (Definition 4.1) and $\tilde\ell_e$ the perspective of $\ell_e$ (Definition 4.4).
--
--   This is the main exactness result of the paper: the nonconvex combinatorial problem (2.1) is equivalent to a mixed-integer program whose only nonconvexity is the integrality of the flows, so it can be solved to global optimality by branch and bound, and its convex relaxation (drop $y_e \in \{0,1\}$) is a lower bound.
--
--   **Formalization Note** Both optimal values are infima in `EReal` and equal $+\infty$ when there is no $s$-$t$ path. The assumption that no edge enters $s$ or leaves $t$ is the "without loss of generality" assumption of p. 7, carried as an explicit hypothesis. The second and third sentences of Theorem 5.7 (recovery of an optimal path) are a separate item, `theorem_5_7_recovery`.
-- source:
--   Marcucci, Umenberger, Parrilo & Tedrake, Shortest Paths in Graphs of Convex Sets, arXiv:2101.11565v5, Theorem 5.7, p. 10 (first sentence)

import Mathlib
import Definitions.Def_ShortestGCS_MICP_Perspective
import Definitions.Def_ShortestGCS_MICP_PerspectiveFun
import Definitions.Def_ShortestGCS_MICP_Setting

namespace ShortestGCS.MICP

/-- Theorem 5.7, arXiv:2101.11565v5, p. 10, first sentence: the MICP (5.5) has optimal value equal
to the SPP in GCS (2.1). Both optimal values are infima in `EReal` (`⊤` when infeasible). Uses the
standing assumptions of §2 (`IsGCS`) and the assumption `|ℰ_s^in| = |ℰ_t^out| = 0` of p. 7. -/
theorem theorem_5_7 {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ} (G : GCS V n) (hG : IsGCS G)
    (hst : NoInSNoOutT G) :
    micpValue G = sppValue G := by sorry

end ShortestGCS.MICP
