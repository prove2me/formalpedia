-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_eq_17
-- name    : RelSmoothFOM.DOptimal.eq_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:36:25.017704+00:00
-- url     : https://prove2.me/theorems/8cfb5e56-c547-4743-b474-167f5dd4d8f9
-- title:
--   Equation (17) — Hadamard Hessian bound by X⁻²
-- statement:
--   For a full-row-rank $H$ and positive $x$, set $X=\operatorname{Diag}(x)$ and $C=H^\top(HXH^\top)^{-1}H$. The matrix inequalities and identity in (17) are
--   $$C\circ C\preceq C\circ X^{-1}\preceq X^{-1}\circ X^{-1}=X^{-2}=\nabla^2h(x),$$
--   where $h(x)=-\sum_j\log x_j$. In particular, $\nabla^2h(x)[v,w]=\sum_jv_jw_j/x_j^2$.
--   The chain supplies the constant $1$ in relative smoothness.
--
--   **Formalization Note** The two Loewner inequalities are positive semidefinite differences. The separate gradient and Hessian items identify $\nabla^2f=C\circ C$.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 341, (17) and proof of Proposition 2.2

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- The Hadamard-product chain (17), including the reference Hessian. -/
theorem eq_17 {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    let C := H.transpose * (H * Matrix.diagonal x * H.transpose)⁻¹ * H
    let Xinv := Matrix.diagonal (fun j => 1 / x j)
    (C.hadamard Xinv - C.hadamard C).PosSemidef ∧
    (Xinv.hadamard Xinv - C.hadamard Xinv).PosSemidef ∧
    Xinv.hadamard Xinv = Matrix.diagonal (fun j => 1 / x j ^ 2) ∧
    (∀ v w : Fin n → ℝ,
      fderiv ℝ (fderiv ℝ logBarrier) x v w =
        ∑ j, v j * w j / x j ^ 2) := by sorry

end RelSmoothFOM.DOptimal
