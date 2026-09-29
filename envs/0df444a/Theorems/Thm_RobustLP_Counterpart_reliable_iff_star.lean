-- Prove2me | Theorems.Thm_RobustLP_Counterpart_reliable_iff_star
-- name    : RobustLP.Counterpart.reliable_iff_star
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:28:02.211302+00:00
-- url     : https://prove2.me/theorems/a5d69ebc-1bc7-40a8-90ff-9d623330c2fd
-- title:
--   A solution is reliable iff it is feasible for (∗)
-- statement:
--   Let an uncertain linear program with data $E,e,A=(a_{ij}),b,\ell,u$ and uncertain-entry sets $J_i$ be given, and let $\epsilon>0$, $\delta>0$. A vector $x$ is **reliable** — feasible for the nominal problem, and for every row $i$ and all $\tilde a_{ij}$ with $|\tilde a_{ij}-a_{ij}|\le\epsilon|a_{ij}|$ ($j\in J_i$) satisfying $\sum_{j\notin J_i}a_{ij}x_j+\sum_{j\in J_i}\tilde a_{ij}x_j\le b_i+\delta\max[1,|b_i|]$ — if and only if $x$ is feasible for
--   $$
--   Ex=e,\qquad Ax\le b,\qquad \sum_j a_{ij}x_j + \epsilon\sum_{j\in J_i}|a_{ij}||x_j| \le b_i+\delta\max[1,|b_i|]\ \ \forall i,\qquad \ell\le x\le u. \tag{$*$}
--   $$
--
--   This identifies the worst case of the interval uncertainty and turns the semi-infinite requirement (ii) into finitely many convex constraints.
--
--   **Formalization Note** The hypotheses $\epsilon>0$ and $\delta>0$ are the paper's standing assumptions on the uncertainty level and the tolerance.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 417, §3.1, 'It is clearly seen that x is reliable if and only if x is a feasible solution of the following optimization problem: … (∗)'

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_Reliable
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts

namespace RobustLP.Counterpart

/-- **Reliability ⇔ (∗)** (Ben-Tal–Nemirovski 2000, §3.1, p. 417). For `ε > 0` and `δ > 0`,
`x` is reliable (conditions (i) and (ii)) if and only if `x` is a feasible solution of (∗). -/
theorem reliable_iff_star {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (x : Fin n → ℝ) :
    L.Reliable ε δ x ↔ L.StarFeasible ε δ x := by sorry

end RobustLP.Counterpart
