-- Prove2me | Theorems.Thm_ProxNewton_Inexact_compGradStep_strongly_monotone
-- name    : ProxNewton.Inexact.compGradStep_strongly_monotone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:39:20.577714+00:00
-- url     : https://prove2.me/theorems/eb0e54ef-9908-4bf0-b76d-295540c9d609
-- title:
--   Lemma 3.9 — $G_{tf}$ is strongly monotone with constant $m/2$ for $t \le 1/L_1$
-- statement:
--   Assume the standing assumptions of §3.4: $g$ is twice continuously differentiable and strongly convex with constant $m>0$, $\nabla g$ is $L_1$-Lipschitz and $\nabla^2 g$ is $L_2$-Lipschitz; $h$ is proper, closed and convex. Let $t$ be a step length with $0 < t \le 1/L_1$. Then the composite gradient step $G_{tf}$ is strongly monotone with constant $m/2$: for all $x, y$,
--   $$(x-y)^T\big(G_{tf}(x) - G_{tf}(y)\big) \ge \frac m2\,\|x-y\|^2. \qquad (3.7)$$
--
--   Strong monotonicity transfers the strong convexity of the smooth part to the composite gradient step; applied to the models $\hat f_k$ it converts a small residual $G_{\hat f_k}(x_k+\Delta x_k)$ into a small distance to the model's minimizer.
--
--   **Formalization Note** $G_{tf}$ is `compGradStep g D h t`. The step-length condition is written $t L_1 \le 1$ together with $t > 0$ (the step $G_{tf}$ is defined with $1/t$). The statement is general in $(g, D, h)$ so that it applies both to $f$ and to the models $\hat f_k$.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 15, Lemma 3.9, Eq. (3.7)

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing

namespace ProxNewton.Inexact

open scoped RealInnerProductSpace

/-- Lemma 3.9: under the standing assumptions of §3.4, the composite gradient step `G_t f` with
step length `0 < t ≤ 1/L1` is strongly monotone with constant `m/2`:
`(x - y)ᵀ(G_t f(x) - G_t f(y)) ≥ (m/2) ‖x - y‖²` (Eq. (3.7)). -/
theorem compGradStep_strongly_monotone {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 t : ℝ)
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (ht : 0 < t) (htL1 : t * L1 ≤ 1) (x y : EuclideanSpace ℝ (Fin n)) :
    m / 2 * ‖x - y‖ ^ 2 ≤ ⟪x - y, compGradStep g D h t x - compGradStep g D h t y⟫ := by sorry

end ProxNewton.Inexact
