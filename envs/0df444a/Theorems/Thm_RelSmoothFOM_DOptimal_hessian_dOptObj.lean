-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_hessian_dOptObj
-- name    : RelSmoothFOM.DOptimal.hessian_dOptObj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:31.104839+00:00
-- url     : https://prove2.me/theorems/ee4a5f8c-39a0-4850-a76a-f2ad6afe38ea
-- title:
--   Proof of Proposition 2.2 — Hessian of the D-optimal objective
-- statement:
--   Let $H\in\mathbb R^{m\times n}$ have rank $m$, let $x_j>0$, and put $X=\operatorname{Diag}(x)$ and $C=H^\top(HXH^\top)^{-1}H$. The first derivative of $f(x)=-\log\det(HXH^\top)$ is differentiable at $x$, and
--   $$\nabla^2 f(x)=C\circ C,\qquad \nabla^2f(x)[v,w]=\sum_{i,j}C_{ij}^2v_iw_j.$$
--   This identifies the Hessian to compare with the log barrier's Hessian in (17).
--
--   **Formalization Note** The Hessian is the second Fréchet derivative. The domain conditions make the matrix inverse and logarithm genuine.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 341, proof of Proposition 2.2, Hessian identity

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- The Hessian identity in the proof of Proposition 2.2. -/
theorem hessian_dOptObj {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    DifferentiableAt ℝ (fderiv ℝ (dOptObj H)) x ∧
      ∀ v w : Fin n → ℝ,
        fderiv ℝ (fderiv ℝ (dOptObj H)) x v w =
          ∑ i, ∑ j,
            (H.transpose * (H * Matrix.diagonal x * H.transpose)⁻¹ * H) i j *
            (H.transpose * (H * Matrix.diagonal x * H.transpose)⁻¹ * H) i j *
            v i * w j := by sorry

end RelSmoothFOM.DOptimal
