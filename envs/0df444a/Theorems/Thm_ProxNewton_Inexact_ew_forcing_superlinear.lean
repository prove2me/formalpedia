-- Prove2me | Theorems.Thm_ProxNewton_Inexact_ew_forcing_superlinear
-- name    : ProxNewton.Inexact.ew_forcing_superlinear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:40:36.138615+00:00
-- url     : https://prove2.me/theorems/396a3775-2ad9-426f-bf30-f1a103b46659
-- title:
--   Theorem 3.11 — forcing terms (2.25) give q-superlinear convergence
-- statement:
--   Assume the standing assumptions of §3.4 ($g$ twice continuously differentiable and strongly convex with constant $m>0$, $\nabla g$ $L_1$-Lipschitz, $\nabla^2 g$ $L_2$-Lipschitz, $h$ proper closed convex with domain $D$), let $x^\star$ be the optimal solution of $\min_x g(x)+h(x)$, and let $M>0$ satisfy $\nabla^2 g(x)\preceq MI$ for all $x$. There is $\delta>0$ with the following property. Consider any run of the inexact proximal Newton method with unit step lengths under the stopping condition (2.24), whose forcing terms are chosen by
--   $$\eta_k = \min\left\{\frac m2,\ \frac{\|G_{\hat f_{k-1}/M}(x_k)-G_{f/M}(x_k)\|}{\|G_{f/M}(x_{k-1})\|}\right\}\quad (k\ge1), \qquad (2.25)$$
--   with any first forcing term $\eta_0\in[0, m/2]$. If $\|x_0 - x^\star\| < \delta$, then $x_k\to x^\star$ q-superlinearly: $x_k\to x^\star$ and, for every $\varepsilon>0$, $\|x_{k+1}-x^\star\|\le\varepsilon\|x_k-x^\star\|$ for all sufficiently large $k$.
--
--   The forcing terms (2.25) need no tuning: they measure how well the previous model predicted the composite gradient step, and they make the subproblems be solved more accurately exactly when the iterates approach $x^\star$.
--
--   **Formalization Note** (2.25) does not define $\eta_0$; the theorem allows any $\eta_0 \in [0, m/2]$, the range (2.25) gives the later terms, and $\delta$ does not depend on $\eta_0$ or on the run. The forcing terms depend on the iterates, unlike in Theorem 3.10. When $G_{f/M}(x_{k-1}) = 0$ the quotient is $0$ in Lean; this happens only at $x_{k-1} = x^\star$.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 18, Theorem 3.11 (forcing terms from p. 9, Eq. (2.25))

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing
import Definitions.Def_ProxNewton_Inexact_Method

namespace ProxNewton.Inexact

open Filter Topology

/-- Theorem 3.11: with the forcing terms (2.25) (and any first forcing term `η_0 ∈ [0, m/2]`),
the inexact proximal Newton method with unit step lengths converges q-superlinearly to `x⋆` from
every start sufficiently close to `x⋆`. -/
theorem ew_forcing_superlinear {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 M : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (hxstar : IsMinimizer g D h xstar) (hM : 0 < M) (hHM : HessianLE g M) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (η : ℕ → ℝ) (x Δ : ℕ → EuclideanSpace ℝ (Fin n)),
      0 ≤ η 0 → η 0 ≤ m / 2 → (∀ k, η (k + 1) = ewForcingTerm g D h M m x k) →
      IsInexactProxNewtonRun g D h M η x Δ → ‖x 0 - xstar‖ < δ →
      Tendsto x atTop (𝓝 xstar) ∧
        ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖x (k + 1) - xstar‖ ≤ ε * ‖x k - xstar‖ := by sorry

end ProxNewton.Inexact
