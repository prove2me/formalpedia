-- Prove2me | Theorems.Thm_ProxNewton_Inexact_compGradStep_model_approx
-- name    : ProxNewton.Inexact.compGradStep_model_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:38:48.634133+00:00
-- url     : https://prove2.me/theorems/77081ae2-c921-4ecc-bb9d-4c272a8364d4
-- title:
--   Lemma 3.8 — $\|G_f(x) - G_{\hat f_k}(x)\| \le \frac{L_2}{2}\|x - x_k\|^2$
-- statement:
--   Assume the standing assumptions of §3.4: $g$ is twice continuously differentiable and strongly convex with constant $m > 0$, $\nabla g$ is $L_1$-Lipschitz and $\nabla^2 g$ is $L_2$-Lipschitz; $h$ is proper, closed and convex with domain $D$. For a point $x_k$ let $\hat f_k = \hat g_k + h$, where $\hat g_k(y) = g(x_k)+\nabla g(x_k)^T(y-x_k)+\frac12(y-x_k)^T\nabla^2 g(x_k)(y-x_k)$. Then for every $x$,
--   $$\|G_f(x) - G_{\hat f_k}(x)\| \le \frac{L_2}{2}\,\|x - x_k\|^2 ,$$
--   where $G_f$ and $G_{\hat f_k}$ are the composite gradient steps with unit step length on $f$ and on $\hat f_k$.
--
--   The model's composite gradient step is a second-order accurate approximation of the true one near $x_k$; this is what makes an inexact solution of the model problem a good step for $f$.
--
--   **Formalization Note** $G_f$ is `compGradStep g D h 1` and $G_{\hat f_k}$ is `compGradStep (quadModel g xk) D h 1`; the statement holds for all $x_k$ and $x$.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 15, Lemma 3.8

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

/-- Lemma 3.8: under the standing assumptions of §3.4, for every model point `x_k` and every
`x`, `‖Gf(x) - G_{f̂_k}(x)‖ ≤ (L2/2) ‖x - x_k‖²`, where `f̂_k = ĝ_k + h` is the model with the
exact Hessian `∇²g(x_k)`. -/
theorem compGradStep_model_approx {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 : ℝ)
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (xk x : EuclideanSpace ℝ (Fin n)) :
    ‖compGradStep g D h 1 x - compGradStep (quadModel g xk) D h 1 x‖ ≤
      L2 / 2 * ‖x - xk‖ ^ 2 := by sorry

end ProxNewton.Inexact
