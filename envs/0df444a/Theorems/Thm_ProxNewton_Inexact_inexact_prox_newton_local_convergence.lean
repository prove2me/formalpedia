-- Prove2me | Theorems.Thm_ProxNewton_Inexact_inexact_prox_newton_local_convergence
-- name    : ProxNewton.Inexact.inexact_prox_newton_local_convergence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:40:00.585105+00:00
-- url     : https://prove2.me/theorems/6d02a907-4323-42bd-a60c-752d9cf00873
-- title:
--   Theorem 3.10 — local q-linear and q-superlinear convergence of the inexact proximal Newton method
-- statement:
--   Assume the standing assumptions of §3.4: $g$ is twice continuously differentiable and strongly convex with constant $m>0$, $\nabla g$ is $L_1$-Lipschitz and $\nabla^2 g$ is $L_2$-Lipschitz; $h$ is proper, closed and convex with domain $D$; $x^\star$ is the optimal solution of $\min_x f(x) = g(x)+h(x)$; and $M > 0$ satisfies $\nabla^2 g(x)\preceq MI$ for all $x$. Consider the inexact proximal Newton method with unit step lengths: $x_0\in D$, and $x_{k+1} = x_k + \Delta x_k \in D$, where $\Delta x_k$ satisfies the adaptive stopping condition
--   $$\|G_{\hat f_k/M}(x_k+\Delta x_k)\| \le \eta_k\,\|G_{f/M}(x_k)\|. \qquad (2.24)$$
--   Then:
--
--   1. **q-linear convergence.** There exist $\bar\eta\in(0, m/2)$, $\delta>0$ and $r\in[0,1)$ such that for every forcing sequence with $0\le\eta_k\le\bar\eta$ for all $k$ and every run with $\|x_0-x^\star\|<\delta$,
--   $$\|x_{k+1}-x^\star\| \le r\,\|x_k - x^\star\|\quad\text{for all } k\ge0 .$$
--   2. **q-superlinear convergence.** For every forcing sequence with $\eta_k\ge0$ and $\eta_k\to0$ there is $\delta > 0$ such that every run with $\|x_0-x^\star\|<\delta$ satisfies $x_k\to x^\star$ and, for every $\varepsilon>0$, $\|x_{k+1}-x^\star\|\le\varepsilon\|x_k-x^\star\|$ for all sufficiently large $k$.
--
--   The result shows that solving the proximal Newton subproblems only to the relative accuracy (2.24) preserves fast local convergence, the composite analogue of the Dembo–Eisenstat–Steihaug theory of inexact Newton methods.
--
--   **Formalization Note** "$x_0$ sufficiently close to $x^\star$" is an existential radius $\delta$ fixed before the run; in part 2 it may depend on the forcing sequence (fixed in advance, independent of the iterates) but not on the run. Part 1 is stated with an existential threshold $\bar\eta$, as the page's "smaller than some $\bar\eta < m/2$" says; the reading "for every $\bar\eta < m/2$" is false: for $n=1$, $g(x)=2x^2$, $h=0$ one has $m=L_1=M=4$, $L_2 = 0$, $G_{f/M}(y) = G_{\hat f_k/M}(y) = y$, and with $\eta_k\equiv 3/2 < m/2$ the steps $x_{k+1} = \frac32 x_k$ satisfy (2.24) and diverge. The constant $M$ of (2.24) is any $M > 0$ with $\nabla^2 g \preceq MI$ (the proof takes $M = L_1$). Rates are stated without quotients.
-- source:
--   Lee, Sun & Saunders, Proximal Newton-type methods for minimizing composite functions, arXiv:1206.1623v13, p. 17, Theorem 3.10

import Mathlib
import Definitions.Def_ProxNewton_Inexact_CompositeStep
import Definitions.Def_ProxNewton_Inexact_Standing
import Definitions.Def_ProxNewton_Inexact_Method

namespace ProxNewton.Inexact

open Filter Topology

/-- Theorem 3.10: local q-linear and q-superlinear convergence of the inexact proximal Newton
method with unit step lengths under the adaptive stopping condition (2.24).
1. There is a threshold `η̄ ∈ (0, m/2)`, a radius `δ > 0` and a ratio `r ∈ [0, 1)` such that
   every run whose forcing terms satisfy `0 ≤ η_k ≤ η̄` and whose start satisfies
   `‖x_0 - x⋆‖ < δ` obeys `‖x_{k+1} - x⋆‖ ≤ r ‖x_k - x⋆‖` for all `k`.
2. For every nonnegative forcing sequence `η_k → 0` there is a radius `δ > 0` such that every run
   with `‖x_0 - x⋆‖ < δ` converges to `x⋆` q-superlinearly. -/
theorem inexact_prox_newton_local_convergence {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n))) (h : EuclideanSpace ℝ (Fin n) → ℝ) (m L1 L2 M : ℝ)
    (xstar : EuclideanSpace ℝ (Fin n))
    (hg : SmoothPartAssumptions g m L1 L2) (hh : IsProperClosedConvex D h)
    (hxstar : IsMinimizer g D h xstar) (hM : 0 < M) (hHM : HessianLE g M) :
    (∃ ηbar : ℝ, 0 < ηbar ∧ ηbar < m / 2 ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ (η : ℕ → ℝ) (x Δ : ℕ → EuclideanSpace ℝ (Fin n)),
        (∀ k, 0 ≤ η k ∧ η k ≤ ηbar) → IsInexactProxNewtonRun g D h M η x Δ →
        ‖x 0 - xstar‖ < δ → ∀ k, ‖x (k + 1) - xstar‖ ≤ r * ‖x k - xstar‖) ∧
    (∀ η : ℕ → ℝ, (∀ k, 0 ≤ η k) → Tendsto η atTop (𝓝 0) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x Δ : ℕ → EuclideanSpace ℝ (Fin n),
        IsInexactProxNewtonRun g D h M η x Δ → ‖x 0 - xstar‖ < δ →
        Tendsto x atTop (𝓝 xstar) ∧
          ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ‖x (k + 1) - xstar‖ ≤ ε * ‖x k - xstar‖) := by sorry

end ProxNewton.Inexact
