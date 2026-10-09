-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_grad_dOptObj
-- name    : RelSmoothFOM.DOptimal.grad_dOptObj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:30.834519+00:00
-- url     : https://prove2.me/theorems/6fc1e78d-0a8a-4947-b7d4-425a826402f1
-- title:
--   Proof of Proposition 2.2 — gradient of the D-optimal objective
-- statement:
--   Let $H\in\mathbb R^{m\times n}$ have rank $m$, let $x_j>0$, and put $X=\operatorname{Diag}(x)$ and $C=H^\top(HXH^\top)^{-1}H$. Then $f(x)=-\log\det(HXH^\top)$ is differentiable at $x$ and
--   $$\nabla f(x)=\operatorname{diag}(-C),\qquad \nabla f(x)\cdot v=\sum_j(-C_{jj})v_j.$$
--   The identity identifies the linear model used by the primal gradient step.
--
--   **Formalization Note** The directional derivative is written as a Fréchet derivative. Positivity of $x$ and full row rank make $HXH^\top$ invertible.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 341, proof of Proposition 2.2, gradient identity

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- The gradient identity in the proof of Proposition 2.2. -/
theorem grad_dOptObj {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    DifferentiableAt ℝ (dOptObj H) x ∧
      ∀ v : Fin n → ℝ,
        fderiv ℝ (dOptObj H) x v =
          ∑ j, -(H.transpose * (H * Matrix.diagonal x * H.transpose)⁻¹ * H) j j * v j := by sorry

end RelSmoothFOM.DOptimal
