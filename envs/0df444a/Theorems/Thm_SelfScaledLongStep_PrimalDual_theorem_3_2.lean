-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_3_2
-- name    : SelfScaledLongStep.PrimalDual.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:04.052158+00:00
-- url     : https://prove2.me/theorems/67550b37-4be5-4775-b347-9860ad9132f7
-- title:
--   Theorem 3.2, p. 9 — unique scaling point w with s = F″(w)x; F′(x) = F″(w)F∗′(s), F″(x) = F″(w)F∗″(s)F″(w)
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$ and conjugate barrier $F_*$. For every pair $x\in\operatorname{int}K$, $s\in\operatorname{int}K^*$ there exists a unique **scaling point** $w\in\operatorname{int}K$ such that
--   $$s=F''(w)x.$$
--   Moreover, for this $w$,
--   $$F'(x)=F''(w)F_*'(s),\qquad F''(x)=F''(w)F_*''(s)F''(w).$$
--
--   The scaling point is what makes primal-dual methods on self-scaled cones symmetric: the single operator $F''(w)$ maps $x$ to $s$ and transports the local geometry at $s$ to that at $x$.
--
--   **Formalization Note** $E^*\cong E=\mathbb R^n$. Existence and uniqueness is stated as `∃!` over points satisfying `IsScalingPoint K F x s w` ($w\in\operatorname{int}K$ and $F''(w)x=s$). The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (the paper derives it, p. 3); `conj K F` is evaluated only at $s\in\operatorname{int}K^*$.
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 9, Theorem 3.2

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Theorem 3.2** (p. 9). For each pair `x ∈ int K`, `s ∈ int K*` there is a unique scaling
point `w ∈ int K` with `s = F''(w)x`. Moreover, for that `w`, `F'(x) = F''(w)F*'(s)` and
`F''(x) = F''(w)F*''(s)F''(w)`, where `F* = conj K F`. -/
theorem theorem_3_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x s : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) :
    (∃! w, IsScalingPoint K F x s w) ∧
    ∀ w, IsScalingPoint K F x s w →
      gradient F x = hess F w (gradient (conj K F) s) ∧
        hess F x = hess F w ∘L hess (conj K F) s ∘L hess F w := by sorry

end SelfScaledLongStep.PrimalDual
