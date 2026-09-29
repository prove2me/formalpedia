-- Prove2me | Theorems.Thm_RobustSDP_Uniqueness_hessian_lagrangian_posDef
-- name    : RobustSDP.Uniqueness.hessian_lagrangian_posDef
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:07:59.027371+00:00
-- url     : https://prove2.me/theorems/c8818bcb-2e27-4da2-a2d9-ae1e61189ea0
-- title:
--   Appendix A — the Hessian of the Lagrangian of (16) is positive definite
-- statement:
--   Assume hypothesis H3(a). Let $x \in \mathbb{R}^m$, $\tau > 0$, $c \in \mathbb{R}^m$ and $Z \in \mathbb{R}^{n\times n}$ with $Z \succeq 0$ and
--   $$\operatorname{Tr} R(x)^T R(x) Z > 0 .$$
--   Consider the Lagrangian of (16) with dual variable $Y = \mathrm{diag}(Z, 0)$,
--   $$\mathcal{L}(y) = c^T x' - \operatorname{Tr} Z\, G(y), \qquad y = (x', \tau') \in \mathbb{R}^m \times \mathbb{R},\quad G(y) = F(x') - \tau' LL^T - \tfrac{1}{\tau'} R(x')^T R(x') .$$
--   Then its Hessian at $(x,\tau)$ is positive definite:
--   $$\nabla^2_{yy}\mathcal{L}(x,\tau)[h,h] > 0 \qquad \text{for every } h \in \mathbb{R}^{m+1},\ h \neq 0 .$$
--
--   At an optimal point with the dual matrix of Appendix A this is the curvature condition (17) of Theorem 4.1, from which the paper derives the quadratic growth condition.
--
--   **Formalization Note** The Hessian is Mathlib's second Fréchet derivative `iteratedFDeriv ℝ 2` evaluated on $(h, h)$; the map is smooth near $(x,\tau)$ because $\tau > 0$. The statement is made at every such $(x,\tau)$, not only at the optimum, since the paper's argument uses only these hypotheses. The multiplier $\mu$ of the scalar constraint $\tau - .99\tau_{\mathrm{opt}} \ge 0$ is $0$ at the optimum and contributes an affine term, so it is omitted. The paper's intermediate display for $-\Phi(\xi,\lambda)$ has a factor slip in the cross term; the conclusion stated here does not depend on it.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), pp. 49–50, Appendix A, last paragraph; p. 39, §4.2, definition of ℒ

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix

namespace RobustSDP.Uniqueness

/-- Appendix A, pp. 49–50: if `τ > 0`, `Z ⪰ 0`, `Tr R(x)ᵀR(x)Z > 0` and H3(a) holds, then the Hessian
at `y = (x, τ)` of the Lagrangian `ℒ(y) = cᵀx − Tr Z G(y)` of (16) (dual variable `Y = diag(Z, 0)`)
is positive definite. -/
theorem hessian_lagrangian_posDef {m n p q : ℕ} (D : SDPData m n p q) (h3a : D.H3a)
    (c : Fin m → ℝ) (Z : Matrix (Fin n) (Fin n) ℝ) (hZ : Z.PosSemidef)
    (x : Fin m → ℝ) (τ : ℝ) (hτ : 0 < τ) (htr : 0 < ((D.R x)ᵀ * D.R x * Z).trace) :
    ∀ h : (Fin m → ℝ) × ℝ, h ≠ 0 →
      0 < iteratedFDeriv ℝ 2
        (fun y : (Fin m → ℝ) × ℝ => c ⬝ᵥ y.1 - (Z * D.G y).trace) (x, τ) ![h, h] := by sorry

end RobustSDP.Uniqueness
