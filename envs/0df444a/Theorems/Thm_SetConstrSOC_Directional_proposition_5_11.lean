-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_proposition_5_11
-- name    : SetConstrSOC.Directional.proposition_5_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:43.072043+00:00
-- url     : https://prove2.me/theorems/55e39ef3-a41d-419f-b6d1-8bb92570db76
-- title:
--   Proposition 5, (11) — second-order tangent chain rule
-- statement:
--   Under the assumptions of Proposition 5, fix the same direction $d$ of metric subregularity and assume $\nabla g(\bar x)d\in T_\Lambda(g(\bar x))$. Then
--
--   $$
--   T_F^2(\bar x;d)=\{w:\nabla g(\bar x)w+\nabla^2g(\bar x)(d,d)\in T_\Lambda^2(g(\bar x);\nabla g(\bar x)d)\}.
--   $$
--
--   The right side is also the zero inverse image of the paper's second-order linearized mapping $D^2M(\bar x,0;d)$.
--
--   **Formalization Note** The printed $g(\bar x)d$ in the direction condition is read as $\nabla g(\bar x)d$, consistent with (10), (11), and the proof.
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 10, Proposition 5, (11)

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

namespace SetConstrSOC.Directional

/-- Proposition 5, (11), p. 10: the second-order tangent set chain rule. -/
theorem proposition_5_11 {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x d : E n) (hx : x ∈ P.feasible) (κ : ℝ)
    (hMS : MetricSubregularDir P.g P.Λ x d κ)
    (hd : (fderiv ℝ P.g x) d ∈ tangentCone P.Λ (P.g x)) :
    secondOrderTangentSet P.feasible x d =
      {w | (fderiv ℝ P.g x) w + ((fderiv ℝ (fderiv ℝ P.g) x) d) d ∈
        secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)} := by sorry

end SetConstrSOC.Directional
