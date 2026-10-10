-- Prove2me | Theorems.Thm_SmoothCCP_PenaltyModel_gradient_formula
-- name    : SmoothCCP.PenaltyModel.gradient_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:46:30.370978+00:00
-- url     : https://prove2.me/theorems/0327a5d1-05da-4784-9fa1-1e83720bac37
-- title:
--   Proof of Proposition 4.1, p. 15 — [∇Q_ε(z)]ᵢ = Γ′_ε(zᵢ − Q_ε(z)) / Σⱼ Γ′_ε(zⱼ − Q_ε(z))
-- statement:
--   Let $\varepsilon>0$, let $\Gamma_\varepsilon$ be built from the quartic kernel (2.6), let $0<\alpha<1$, $N\ge1$ and $(1-\alpha)N\notin\mathbb Z$, and let $Q_\varepsilon:\mathbb R^N\to\mathbb R$ be the smoothed $(1-\alpha)$-quantile of (2.3). Then $Q_\varepsilon$ is differentiable at every $z\in\mathbb R^N$, with partial derivatives
--   $$
--   [\nabla Q_\varepsilon(z)]_i=\frac{\Gamma_\varepsilon'(z_i-Q_\varepsilon(z))}{\sum_{j=1}^N\Gamma_\varepsilon'(z_j-Q_\varepsilon(z))},\qquad i=1,\dots,N .
--   $$
--
--   This is the formula from which Proposition 4.1 derives the boundedness and Lipschitz continuity of $\nabla Q_\varepsilon$; it is also the gradient supplied to nonlinear solvers through (4.2).
--
--   **Formalization Note** The derivative is stated as a Fréchet derivative on `Fin N → ℝ`, equal to $\sum_i [\nabla Q_\varepsilon(z)]_i\,e_i^{\mathsf T}$ with $e_i^{\mathsf T}$ the $i$-th coordinate projection. $\Gamma_\varepsilon'$ is `deriv` of the smoothed indicator, which is differentiable for the quartic kernel, so it is the true derivative.
-- source:
--   Peña-Ordieres, Luedtke, Wächter, Solving chance-constrained problems via a smooth sample-based nonlinear approximation, arXiv:1905.07377v2, proof of Proposition 4.1, p. 15, first display

import Mathlib
import Definitions.Def_SmoothCCP_PenaltyModel_Setting

namespace SmoothCCP.PenaltyModel

/-- Proof of Proposition 4.1, arXiv:1905.07377v2, p. 15: with γ_ε the quartic kernel (2.6) and
(1 − α)N ∉ ℤ, Q_ε is differentiable at every z ∈ ℝᴺ with
[∇Q_ε(z)]ᵢ = Γ′_ε(zᵢ − Q_ε(z)) / Σⱼ Γ′_ε(zⱼ − Q_ε(z)). -/
theorem gradient_formula {N : ℕ} (ε α : ℝ) (hε : 0 < ε) (hα0 : 0 < α) (hα1 : α < 1)
    (hN : 1 ≤ N) (hαN : ∀ k : ℤ, (1 - α) * N ≠ k) (z : Fin N → ℝ) :
    HasFDerivAt (smoothQuantile ε (quarticGamma ε) α)
      (∑ i : Fin N,
        (deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z i - smoothQuantile ε (quarticGamma ε) α z) /
          ∑ j : Fin N, deriv (SmoothCCP.Feasibility.Gam ε (quarticGamma ε)) (z j - smoothQuantile ε (quarticGamma ε) α z)) •
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i)
      z := by sorry

end SmoothCCP.PenaltyModel
