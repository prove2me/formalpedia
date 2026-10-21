-- Prove2me | Theorems.Thm_SetConstrSOC_Directional_proposition_5_12
-- name    : SetConstrSOC.Directional.proposition_5_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:00.860218+00:00
-- url     : https://prove2.me/theorems/363a6ffa-b0b7-463c-b0e2-5d127ebbdb42
-- title:
--   Proposition 5, (12) — second-order error bound
-- statement:
--   Under the assumptions of Proposition 5, fix its metric-subregularity direction $d$ with $\nabla g(\bar x)d\in T_\Lambda(g(\bar x))$. For every $w\in\mathbb R^n$,
--
--   $$
--   \operatorname{dist}(w,T_F^2(\bar x;d))\le\kappa\operatorname{dist}\bigl(\nabla g(\bar x)w+\nabla^2g(\bar x)(d,d),T_\Lambda^2(g(\bar x);\nabla g(\bar x)d)\bigr).
--   $$
--
--   The right side is equivalently $\kappa\operatorname{dist}(0,D^2M(\bar x,0;d)(w))$. This estimate supplies the error bound for the second-order linearized constraint.
--
--   **Formalization Note** The paper's printed $x$ and $\nabla g^2$ in (12) are read as $\bar x$ and $\nabla^2g$. Both distances allow $+\infty$ for an empty tangent set. The constant $\kappa$ is any admissible constant in (7).
-- source:
--   Gfrerer, Ye & Zhou, Second-order optimality conditions for non-convex set-constrained optimization problems, arXiv:1911.04076v2, p. 10, Proposition 5, (12); printed slips corrected as explained in natural-language statement

import Mathlib
import Definitions.Def_SetConstrSOC_Directional_Model

namespace SetConstrSOC.Directional

/-- Proposition 5, (12), p. 10: the second-order error bound. -/
theorem proposition_5_12 {n m : ℕ} (P : Problem n m) (hP : P.Standing)
    (x d : E n) (hx : x ∈ P.feasible) (κ : ℝ)
    (hMS : MetricSubregularDir P.g P.Λ x d κ)
    (hd : (fderiv ℝ P.g x) d ∈ tangentCone P.Λ (P.g x)) (w : E n) :
    EMetric.infEdist w (secondOrderTangentSet P.feasible x d) ≤
      ENNReal.ofReal κ *
        EMetric.infEdist
          ((fderiv ℝ P.g x) w + ((fderiv ℝ (fderiv ℝ P.g) x) d) d)
          (secondOrderTangentSet P.Λ (P.g x) ((fderiv ℝ P.g x) d)) := by sorry

end SetConstrSOC.Directional
