-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_proposition_6_1
-- name    : SelfScaledLongStep.PrimalDual.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:23:24.944277+00:00
-- url     : https://prove2.me/theorems/ab45b647-5360-487c-886a-957bcc69ace3
-- title:
--   Proposition 6.1, p. 23 — for surjective A and w ∈ int K, the system Ap = 0, A∗y + F″(w)p = u has a unique solution
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$, let $A:E\to Y^*$ be a surjective linear operator (6.1) with adjoint $A^*$, and fix $w\in\operatorname{int}K$. For every $u\in E^*$ the linear system
--   $$Ap=0,\qquad A^*y+F''(w)p=u\qquad(6.4)$$
--   has a unique solution $(y,p)\in Y\times E$.
--
--   The solution $p$ is the projection of $u$ into the kernel of $A$ with respect to the positive definite operator $F''(w)$; the search directions of all the algorithms of the paper, including the joint-scaling direction (8.1), are such projections.
--
--   **Formalization Note** $E=E^*=\mathbb R^n$, $Y=Y^*=\mathbb R^m$, and $A^*$ is `ContinuousLinearMap.adjoint A`. The system is the definition `IsProjection F A w u y p`, and uniqueness is `∃!` over pairs. The other standing assumptions of §6, (6.2)–(6.3), are not used and not assumed. The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 23, Proposition 6.1, (6.4); assumption (6.1), p. 22

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures
import Definitions.Def_SelfScaledLongStep_PrimalDual_Defs

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Proposition 6.1** (p. 23). Under (6.1) (`A : E → Y*` surjective) and for a fixed
`w ∈ int K`, for every `u ∈ E*` the system (6.4) `A p = 0`, `A* y + F''(w) p = u` has a unique
solution `(y, p)`. -/
theorem proposition_6_1 {n m : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) (hA : Function.Surjective A)
    (w : EuclideanSpace ℝ (Fin n)) (hw : w ∈ interior K) (u : EuclideanSpace ℝ (Fin n)) :
    ∃! yp : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n),
      IsProjection F A w u yp.1 yp.2 := by sorry

end SelfScaledLongStep.PrimalDual
