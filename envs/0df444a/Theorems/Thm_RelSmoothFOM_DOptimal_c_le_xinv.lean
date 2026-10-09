-- Prove2me | Theorems.Thm_RelSmoothFOM_DOptimal_c_le_xinv
-- name    : RelSmoothFOM.DOptimal.c_le_xinv
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:34.747909+00:00
-- url     : https://prove2.me/theorems/29be4ab9-151c-4191-b8c0-c7f85503d175
-- title:
--   Proof of Proposition 2.2 — matrix bound C ⪯ X⁻¹
-- statement:
--   For a full-row-rank $H\in\mathbb R^{m\times n}$ and $x_j>0$, write $X=\operatorname{Diag}(x)$ and $C=H^\top(HXH^\top)^{-1}H$. Then
--   $$C\preceq X^{-1},$$
--   meaning that $X^{-1}-C$ is positive semidefinite. The bound is the matrix input for both Hadamard-product inequalities in (17).
--
--   **Formalization Note** Loewner order is represented by positive semidefiniteness of the difference, rather than coordinatewise matrix order.
-- source:
--   Lu, Freund & Nesterov, Relatively smooth convex optimization by first-order methods, and applications, SIAM J. Optim. 28 (2018), p. 341, proof of Proposition 2.2, C ⪯ X⁻¹

import Mathlib
import Definitions.Def_RelSmoothFOM_DOptimal_Setting

namespace RelSmoothFOM.DOptimal

/-- The Loewner inequality C ⪯ X⁻¹ in the proof of Proposition 2.2. -/
theorem c_le_xinv {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ)
    (hH : H.rank = m) (x : Fin n → ℝ) (hx : ∀ j, 0 < x j) :
    (Matrix.diagonal (fun j => 1 / x j) -
      H.transpose * (H * Matrix.diagonal x * H.transpose)⁻¹ * H).PosSemidef := by sorry

end RelSmoothFOM.DOptimal
