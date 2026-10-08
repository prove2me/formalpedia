-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_4_1
-- name    : SelfScaledLongStep.PrimalDual.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:21:49.156054+00:00
-- url     : https://prove2.me/theorems/f41c7306-7b1a-4f86-92ae-d74bc5d573f4
-- title:
--   Theorem 4.1, p. 14 — F″(x)/(1 + ασ_x(−p))² ⪯ F″(x − αp) ⪯ F″(x)/(1 − ασ_x(p))² for α ∈ [0, 1/σ_x(p))
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$, let $x\in\operatorname{int}K$ and $p\in E$, and let
--   $$\sigma_x(p)=\min\{\beta\ge0:\beta x-p\in K\},$$
--   so that $1/\sigma_x(p)$ is the largest step from $x$ along $-p$ that stays in $K$ ($+\infty$ if $\sigma_x(p)=0$). For every $\alpha\in[0,1/\sigma_x(p))$ the point $x-\alpha p$ lies in $\operatorname{int}K$ and, in the positive semidefinite order,
--   $$\frac{1}{(1+\alpha\sigma_x(-p))^2}F''(x)\preceq F''(x-\alpha p)\preceq\frac{1}{(1-\alpha\sigma_x(p))^2}F''(x).\qquad(4.6)$$
--
--   For a general self-concordant barrier such a comparison holds only inside the unit Dikin ellipsoid; for a self-scaled barrier it holds along the whole segment to the boundary. This is what makes long steps analysable.
--
--   **Formalization Note** The step range is encoded as $0\le\alpha$ and $\alpha\,\sigma_x(p)<1$, exact also when $\sigma_x(p)=0$. The first conclusion, $x-\alpha p\in\operatorname{int}K$, is the sentence following the definition of $\sigma_x$ on p. 12, added so that the Hessian at $x-\alpha p$ is meaningful. The operator inequalities are quadratic-form inequalities for every $v$. $\sigma_x$ is the published `sigma K x` (an infimum, equal to the minimum at an interior centre). The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 14, Theorem 4.1, (4.6); setting of p. 12

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Theorem 4.1** (p. 14), with the setting of p. 12 (`x ∈ int K`, `p ∈ E`). For every
`α ∈ [0, 1/σ_x(p))` (encoded `0 ≤ α`, `α σ_x(p) < 1`; `1/0 = +∞`), the point `x − αp` lies in
`int K` (the sentence after the definition of `σ_x`, p. 12) and (4.6) holds in the positive
semidefinite order:
`(1 + ασ_x(−p))⁻² F''(x) ≤ F''(x − αp) ≤ (1 − ασ_x(p))⁻² F''(x)`. -/
theorem theorem_4_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K) (α : ℝ) (hα0 : 0 ≤ α)
    (hα : α * sigma K x p < 1) :
    x - α • p ∈ interior K ∧
    ∀ v : EuclideanSpace ℝ (Fin n),
      (1 / (1 + α * sigma K x (-p)) ^ 2) * ⟪hess F x v, v⟫_ℝ ≤ ⟪hess F (x - α • p) v, v⟫_ℝ ∧
        ⟪hess F (x - α • p) v, v⟫_ℝ ≤ (1 / (1 - α * sigma K x p) ^ 2) * ⟪hess F x v, v⟫_ℝ := by sorry

end SelfScaledLongStep.PrimalDual
