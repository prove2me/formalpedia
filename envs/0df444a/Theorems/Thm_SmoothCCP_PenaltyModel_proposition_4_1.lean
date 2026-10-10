-- Prove2me | Theorems.Thm_SmoothCCP_PenaltyModel_proposition_4_1
-- name    : SmoothCCP.PenaltyModel.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:36.981035+00:00
-- url     : https://prove2.me/theorems/0df55af7-6634-47e5-9d0b-7dae75cbcb06
-- title:
--   Proposition 4.1 — with the quartic kernel and (1 − α)N ∉ ℤ, Q_ε has bounded Lipschitz continuous gradients
-- statement:
--   Let $\varepsilon>0$, let $\gamma_\varepsilon$ be the quartic kernel (2.6), let $0<\alpha<1$, $N\ge1$, and suppose $(1-\alpha)N\notin\mathbb Z$. Let $Q_\varepsilon:\mathbb R^N\to\mathbb R$ be the smoothed $(1-\alpha)$-quantile of (2.3). Then $Q_\varepsilon$ is differentiable on $\mathbb R^N$, and there are constants $B$ and $K$ such that
--   $$
--   \|\nabla Q_\varepsilon(z)\|\le B\quad\text{and}\quad\|\nabla Q_\varepsilon(z)-\nabla Q_\varepsilon(w)\|\le K\|z-w\|\qquad\text{for all }z,w\in\mathbb R^N .
--   $$
--
--   Both properties are used in the proof of Proposition 5.3: the boundedness to control the linearization error of $\widetilde Q_\varepsilon$ in its second argument, and the Lipschitz constant $L_Q$ in a Taylor estimate. By the chain rule the same smoothness transfers to the constraint $q(x)=Q_\varepsilon(C^N(x))$ when $C(\cdot,\xi_i)$ is smooth.
--
--   **Formalization Note** $\mathbb R^N$ is `Fin N → ℝ` with its sup norm and the gradient is the Fréchet derivative with the operator norm. All norms on $\mathbb R^N$ are equivalent and $B$, $K$ are existential, so the choice of norm does not change the statement. Both constants are quantified before $z,w$.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, Proposition 4.1, p. 15

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace SmoothCCP.PenaltyModel

/-- Proposition 4.1, arXiv:1905.07377v2, p. 15: if γ_ε is the quartic kernel (2.6) and (1 − α)N ∉ ℤ,
then Q_ε : ℝᴺ → ℝ is differentiable with bounded, Lipschitz continuous gradient (both constants
uniform in z). -/
theorem proposition_4_1 {N : ℕ} (ε α : ℝ) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1)
    (hN : 1 ≤ N) (hαN : ∀ k : ℤ, (1 - α) * N ≠ k) :
    Differentiable ℝ (smoothQuantile (N := N) ε (quarticGamma ε) α) ∧
      (∃ B : ℝ, ∀ z : Fin N → ℝ, ‖fderiv ℝ (smoothQuantile ε (quarticGamma ε) α) z‖ ≤ B) ∧
      (∃ K : ℝ, ∀ z w : Fin N → ℝ,
        ‖fderiv ℝ (smoothQuantile ε (quarticGamma ε) α) z -
            fderiv ℝ (smoothQuantile ε (quarticGamma ε) α) w‖ ≤ K * ‖z - w‖) := by sorry

end SmoothCCP.PenaltyModel
