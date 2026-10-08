-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_theorem_5_2
-- name    : SelfScaledLongStep.PrimalDual.theorem_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:37.588547+00:00
-- url     : https://prove2.me/theorems/d4143ad3-d6f5-42f8-ae11-d556ad2c910f
-- title:
--   Theorem 5.2, p. 20 — ⟨F′(x), F∗′(s)⟩ ≥ ν(ν − 1)/⟨s, x⟩ + (3/4)σ²_x(w), with w the scaling point
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$ and conjugate barrier $F_*$. For every $x\in\operatorname{int}K$ and $s\in\operatorname{int}K^*$,
--   $$\langle F'(x),F_*'(s)\rangle\ge\frac{\nu(\nu-1)}{\langle s,x\rangle}+\frac34\,\sigma_x^2(w),\qquad(5.6)$$
--   where $w\in\operatorname{int}K$ is the scaling point with $s=F''(w)x$ and $\sigma_x(w)=\min\{\beta\ge0:\beta x-w\in K\}$.
--
--   This extends Lemma 2.5 of Kojima, Mizuno and Yoshise (1991) to self-scaled cones; it is the inequality that yields a constant decrease of the primal-dual potential in Theorem 8.2.
--
--   **Formalization Note** The scaling point is a binder $w$ with `IsScalingPoint K F x s w` ($w\in\operatorname{int}K$, $F''(w)x=s$); its existence is Theorem 3.2. $F_*$ is `conj K F`, evaluated only at $s\in\operatorname{int}K^*$; $\sigma_x(w)$ is `sigma K x w`. The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, p. 20, Theorem 5.2, (5.6)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Theorem 5.2** (p. 20). For `x ∈ int K`, `s ∈ int K*` and the scaling point `w ∈ int K`
with `s = F''(w)x`, (5.6): `⟨F'(x), F*'(s)⟩ ≥ ν(ν − 1)/⟨s, x⟩ + (3/4)σ_x²(w)`,
where `F* = conj K F` and `σ_x(w) = sigma K x w`. -/
theorem theorem_5_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν)
    (x s w : EuclideanSpace ℝ (Fin n)) (hx : x ∈ interior K)
    (hs : s ∈ interior (ConvexOptimization.dualCone K)) (hw : IsScalingPoint K F x s w) :
    ν * (ν - 1) / ⟪s, x⟫_ℝ + 3 / 4 * (sigma K x w) ^ 2 ≤
      ⟪gradient F x, gradient (conj K F) s⟫_ℝ := by sorry

end SelfScaledLongStep.PrimalDual
