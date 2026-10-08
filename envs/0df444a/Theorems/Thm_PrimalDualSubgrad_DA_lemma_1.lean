-- Prove2me | Theorems.Thm_PrimalDualSubgrad_DA_lemma_1
-- name    : PrimalDualSubgrad.DA.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:46:18.750974+00:00
-- url     : https://prove2.me/theorems/4a923a2f-a9b6-464c-9688-80cf15f18021
-- title:
--   Lemma 1 — V_β is convex and differentiable with 1/(βσ)-Lipschitz gradient π_β(s) − x₀
-- statement:
--   Fix a prox setting $(Q, d, \sigma, x_0)$ in a finite-dimensional normed space $E$, an argmin map $\pi$, and $\beta > 0$. Then the function $V_\beta(s) = \max_{x \in Q}\{\langle s, x - x_0\rangle - \beta d(x)\}$ is convex and differentiable on $E^*$, its gradient at $s$ is $\nabla V_\beta(s) = \pi_\beta(s) - x_0$ (2.4), where $\pi_\beta(s) = \arg\min_{x\in Q}\{-\langle s,x\rangle + \beta d(x)\} \in Q$, and the gradient is Lipschitz continuous with constant $1/(\beta\sigma)$:
--   $$\|\nabla V_\beta(s_1) - \nabla V_\beta(s_2)\| \le \frac{1}{\beta\sigma}\|s_1 - s_2\|_*, \qquad s_1, s_2 \in E^*. \qquad (2.3)$$
--
--   This is the smoothness of the dual function on which the Dual Averaging analysis rests.
--
--   **Formalization Note** The gradient, an element of $E^{**}$, is identified with a vector of $E$: the Fréchet derivative of $V_\beta$ at $s$ is the functional $\delta \mapsto \langle \delta, \pi_\beta(s) - x_0\rangle$. The page says "$\nabla V_\beta(s)$ belongs to $Q$", which is true only for $x_0 = 0$; what holds and what is stated is $\pi_\beta(s) \in Q$ (this conjunct follows directly from the argmin-map hypothesis).
-- source:
--   Nesterov, Primal-dual subgradient methods for convex problems, Math. Program. 120 (2009), p. 7, Lemma 1, (2.3), (2.4)

import Mathlib
import Definitions.Def_PrimalDualSubgrad_DA_ProxSetting

namespace PrimalDualSubgrad.DA

/-- Lemma 1 (p. 7). For `β > 0`, `V_β` is convex and differentiable on `E*`, its gradient at
`s` is the evaluation at `π_β(s) − x0` (the identification `E** = E`), the gradient is
Lipschitz with constant `1/(βσ)` (2.3), and `π_β(s) ∈ Q` (2.4). -/
theorem lemma_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (P : ProxSetting E) (π : ℝ → StrongDual ℝ E → E) (hπ : IsProxMap P π)
    (β : ℝ) (hβ : 0 < β) :
    ConvexOn ℝ Set.univ (V P β) ∧
      (∀ s : StrongDual ℝ E,
        HasFDerivAt (V P β) (ContinuousLinearMap.apply ℝ ℝ (π β s - P.x0)) s) ∧
      (∀ s₁ s₂ : StrongDual ℝ E, ‖π β s₁ - π β s₂‖ ≤ 1 / (β * P.σ) * ‖s₁ - s₂‖) ∧
      (∀ s : StrongDual ℝ E, π β s ∈ P.Q) := by sorry

end PrimalDualSubgrad.DA
