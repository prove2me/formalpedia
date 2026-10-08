-- Prove2me | Theorems.Thm_SelfScaledLongStep_PrimalDual_corollary_4_1
-- name    : SelfScaledLongStep.PrimalDual.corollary_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:09.593921+00:00
-- url     : https://prove2.me/theorems/40aa2231-6c45-420a-b460-f117c7da850c
-- title:
--   Corollary 4.1 (i)–(ii), pp. 15–16 — F″(x + v) ⪯ F″(x) ⪯ F″(x − (α/σ_x(v))v), and F″(x) ⪯ σ_x²(w)F″(w)
-- statement:
--   Let $K$ be a self-scaled cone with a $\nu$-self-scaled barrier $F$; inequalities are in the positive semidefinite order.
--
--   1. For every $x\in\operatorname{int}K$, $v\in K$ and $\alpha\in[0,1)$,
--   $$F''(x+v)\preceq F''(x)\preceq F''\Big(x-\frac{\alpha}{\sigma_x(v)}v\Big).$$
--   2. For all $x,w\in\operatorname{int}K$,
--   $$F''(x)\preceq\sigma_x^2(w)\,F''(w).$$
--
--   Part (ii) bounds the local geometry at one interior point by that at another, with a factor given by the distance measure $\sigma_x(w)$; it is the estimate (8.4) of the analysis of the primal-dual method.
--
--   **Formalization Note** Inequalities are stated as quadratic forms. In (i), $v=0$ gives $\sigma_x(0)=0$ and Lean's convention $\alpha/0=0$ turns the right inequality into $F''(x)\preceq F''(x)$, which is true; every $v\in K\setminus\{0\}$ has $\sigma_x(v)>0$ by pointedness, so no hypothesis is added. Part (iii) of the corollary is posed in another mission of this series. The barrier is nondegenerate as in the published setting; $\nu\ge1$ is a binder (derived in the paper, p. 3).
-- source:
--   Nesterov & Todd, Self-scaled barriers and interior-point methods for convex programming, Math. Oper. Res. 22(1) (1997) 1–42, pp. 15–16, Corollary 4.1 (i)–(ii)

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_SelfScaledIPM_ShortStep_Setting
import Definitions.Def_SelfScaledIPM_ShortStep_Measures

open scoped InnerProductSpace
open SelfScaledIPM.ShortStep

namespace SelfScaledLongStep.PrimalDual

/-- **Corollary 4.1 (i)–(ii)** (pp. 15–16), in the positive semidefinite order (quadratic forms).
(i) For `x ∈ int K`, `v ∈ K` and `α ∈ [0, 1)`: `F''(x + v) ≤ F''(x) ≤ F''(x − (α/σ_x(v)) v)`.
(For `v = 0`, `σ_x(0) = 0` and Lean's `α / 0 = 0` makes the right inequality `F''(x) ≤ F''(x)`;
every `v ∈ K \ {0}` has `σ_x(v) > 0`.)
(ii) For `x, w ∈ int K`: `F''(x) ≤ σ_x(w)² F''(w)`. -/
theorem corollary_4_1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsProperCone K)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) (hν : 1 ≤ ν) (hF : IsSelfScaledBarrier K F ν) :
    (∀ x ∈ interior K, ∀ v ∈ K, ∀ α : ℝ, 0 ≤ α → α < 1 → ∀ u : EuclideanSpace ℝ (Fin n),
      ⟪hess F (x + v) u, u⟫_ℝ ≤ ⟪hess F x u, u⟫_ℝ ∧
        ⟪hess F x u, u⟫_ℝ ≤ ⟪hess F (x - (α / sigma K x v) • v) u, u⟫_ℝ) ∧
    (∀ x ∈ interior K, ∀ w ∈ interior K, ∀ u : EuclideanSpace ℝ (Fin n),
      ⟪hess F x u, u⟫_ℝ ≤ (sigma K x w) ^ 2 * ⟪hess F w u, u⟫_ℝ) := by sorry

end SelfScaledLongStep.PrimalDual
