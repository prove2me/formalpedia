-- Prove2me | Theorems.Thm_RossSolandGAP_Bound_agent_subproblem_value
-- name    : RossSolandGAP.Bound.agent_subproblem_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:11:18.632919+00:00
-- url     : https://prove2.me/theorems/b5d52ead-209e-4976-9a18-8b053d3721c5
-- title:
--   §2, p. 96 — at λ_j = c_2j agent i's subproblem on the (PR) pattern has value −Σ_{J_i} p_j + z*_i
-- statement:
--   Let $m\ge2$, let $j\mapsto i_j$ be a cheapest-agent selection and use the notation $J_i$, $I'$, $d_i$, $p_j$, $c_{2j}$ and (PK$_i$) of the paper. Fix an agent $i$ and consider agent $i$'s part of (PR$_\lambda$) at $\lambda=c_2$, restricted to the (PR) pattern:
--
--   $$
--   \min\ \sum_{j\in J}(c_{ij}-c_{2j})v_j\quad\text{s.t.}\quad\sum_{j\in J}r_{ij}v_j\le b_i,\ v_j\in\{0,1\},\ v_j=0\text{ if }i_j\ne i .
--   $$
--
--   1. If $i\in I'$ and $y^*_i$ is an optimal solution of (PK$_i$) with value $z^*_i$, the minimum is $-\sum_{j\in J_i}p_j+z^*_i$ (a lower bound on every feasible $v$, attained by some feasible $v$).
--   2. If $i\notin I'$, the minimum is $-\sum_{j\in J_i}p_j$ (attained at $v_j=1$ on $J_i$).
--
--   Summed over agents and added to $\sum_jc_{2j}$, this gives $\sum_j c_{i_jj}+\sum_{i\in I'}z^*_i=\mathrm{LB}$. It is the step "solving (PR) and subsequently solving (PK$_i$) for all $i\in I'$ yields a bound equal to that provided by (PR$_\lambda$)".
--
--   **Formalization Note** $z^*_i$ is the (PK$_i$) objective of a given optimal solution `y`. Agents and tasks are 0-based.
-- source:
--   Ross & Soland, A Branch and Bound Algorithm for the Generalized Assignment Problem, Mathematical Programming 8, 1975, p. 96, §2, second paragraph, second and third sentences

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model
open Finset

namespace RossSolandGAP.Bound

theorem agent_subproblem_value {m n : ℕ} (hm : 1 < m) (c r : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ) (a : Fin n → Fin m) (ha : IsCheapest c a) (i : Fin m) :
    (i ∈ Iprime r b a → ∀ y, IsOptPK hm c r b a i y →
      (∀ v, KnapFeasible r b i v → (∀ j, a j ≠ i → v j = 0) →
        -(∑ j ∈ Jset a i, pen hm c a j) + pkObj hm c a i y ≤
          ∑ j, (c i j - c2 hm c a j) * v j) ∧
      ∃ v, KnapFeasible r b i v ∧ (∀ j, a j ≠ i → v j = 0) ∧
        ∑ j, (c i j - c2 hm c a j) * v j =
          -(∑ j ∈ Jset a i, pen hm c a j) + pkObj hm c a i y) ∧
    (i ∉ Iprime r b a →
      (∀ v, KnapFeasible r b i v → (∀ j, a j ≠ i → v j = 0) →
        -(∑ j ∈ Jset a i, pen hm c a j) ≤ ∑ j, (c i j - c2 hm c a j) * v j) ∧
      ∃ v, KnapFeasible r b i v ∧ (∀ j, a j ≠ i → v j = 0) ∧
        ∑ j, (c i j - c2 hm c a j) * v j = -(∑ j ∈ Jset a i, pen hm c a j)) := by sorry

end RossSolandGAP.Bound
