-- Prove2me | Theorems.Thm_SelfScaledIPM_FuncProx_theorem_3_11
-- name    : SelfScaledIPM.FuncProx.theorem_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:18:04.241321+00:00
-- url     : https://prove2.me/theorems/8215e6b4-98fe-4c44-8bd4-48946a92b481
-- title:
--   Theorem 3.11, p. 12 — parallelogram rule F(x − αp) + F(x + βp) = F(x) + F(x + (β − α)p + ½αβ[F″(x)]⁻¹F‴(x)[p,p])
-- statement:
--   Let $K$ be a proper cone with a $\nu$-self-scaled barrier $F$. Let $x\in\operatorname{int}K$, $p\in E$, and let $\alpha,\beta>0$ be such that $x-\alpha p\in\operatorname{int}K$ and $x+\beta p\in\operatorname{int}K$. Then the point
--   $$v=x+(\beta-\alpha)p+\tfrac12\alpha\beta\,[F''(x)]^{-1}F'''(x)[p,p]$$
--   lies in $\operatorname{int}K$, and
--   $$F(x-\alpha p)+F(x+\beta p)=F(x)+F(v).$$
--
--   This "parallelogram rule" converts a sum of barrier values at two points of a line into a single barrier value, and is the identity behind the exact formula (5.8) for the change of $\gamma_F$ along the affine-scaling direction.
--
--   **Formalization Note** The vector $r=[F''(x)]^{-1}F'''(x)[p,p]$ is given by the equation $F''(x)r=F'''(x)[p,p]$ ($F''(x)$ is invertible). The membership $v\in\operatorname{int}K$ is proved on the page and is stated so that the identity is about a point of the barrier's domain.
-- source:
--   Nesterov & Todd, Primal-dual interior-point methods for self-scaled cones, SIAM J. Optim. 8 (1998) 324–364 (authors' copy, Cornell eCommons), p. 12, Theorem 3.11

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_FuncProx_Setting

open scoped InnerProductSpace

namespace SelfScaledIPM.FuncProx

/-- **Theorem 3.11** (p. 12, "parallelogram rule"). Let `x ∈ int K`, `p ∈ E`, `α, β > 0` with
`x − αp ∈ int K` and `x + βp ∈ int K`, and let `r = [F''(x)]⁻¹F'''(x)[p, p]` (given by
`F''(x) r = F'''(x)[p, p]`). Then `v := x + (β − α)p + ½αβ r` lies in `int K` and
`F(x − αp) + F(x + βp) = F(x) + F(v)`. -/
theorem theorem_3_11
    {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : SelfScaledIPM.ShortStep.IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : SelfScaledIPM.ShortStep.IsSelfScaledBarrier K F ν)
    (x p : EuclideanSpace ℝ (Fin n)) (α β : ℝ) (hx : x ∈ interior K) (hα : 0 < α) (hβ : 0 < β)
    (hxα : x - α • p ∈ interior K) (hxβ : x + β • p ∈ interior K)
    (r : EuclideanSpace ℝ (Fin n)) (hr : SelfScaledIPM.ShortStep.hess F x r = third F x p p) :
    x + (β - α) • p + ((1 / 2 : ℝ) * α * β) • r ∈ interior K ∧
      F (x - α • p) + F (x + β • p) = F x + F (x + (β - α) • p + ((1 / 2 : ℝ) * α * β) • r) := by sorry

end SelfScaledIPM.FuncProx
