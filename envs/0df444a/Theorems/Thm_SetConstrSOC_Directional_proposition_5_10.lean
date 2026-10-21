-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_proposition_5_10
-- name    : SetConstrSOC.Directional.proposition_5_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:33.728455+00:00
-- url     : https://prove2.me/theorems/dcef78a8-3bb4-42cf-aa05-dc31089a3966
-- title:
--   Proposition 5, (10) — first-order tangent chain rule
-- statement:
--   Consider problem (P) with $f,g$ twice continuously differentiable and $\Lambda$ closed. Let $\bar x\in F$, and suppose that the feasible mapping $g(x)-\Lambda$ is metrically subregular at $(\bar x,0)$ in direction $d$. Then
--
--   $$
--   d\in T_F(\bar x)\quad\Longleftrightarrow\quad\nabla g(\bar x)d\in T_\Lambda(g(\bar x)).
--   $$
--
--   This identifies feasible first-order directions with directions that satisfy the linearized set constraint.
--
--   **Formalization Note** The statement carries a positive admissible subregularity constant $\kappa$; its value is irrelevant to this equivalence.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 10, Proposition 5, (10)

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

namespace SetConstrSOC.Directional

/-- Proposition 5, (10), p. 10: the tangent cone chain rule. -/
theorem proposition_5_10 {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x d : E n) (hx : x ∈ P.feasible) (κ : ℝ)
    (hMS : MetricSubregularDir P.g P.Λ x d κ) :
    d ∈ tangentCone P.feasible x ↔
      (fderiv ℝ P.g x) d ∈ tangentCone P.Λ (P.g x) := by sorry

end SetConstrSOC.Directional
