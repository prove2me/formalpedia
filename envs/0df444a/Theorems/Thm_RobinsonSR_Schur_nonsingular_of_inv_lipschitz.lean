-- Prove2me | Theorems.Thm_RobinsonSR_Schur_nonsingular_of_inv_lipschitz
-- name    : RobinsonSR.Schur.nonsingular_of_inv_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:11:12.870038+00:00
-- url     : https://prove2.me/theorems/6be3786e-5305-4787-89af-a730d79130a1
-- title:
--   Global Lipschitz invertibility forces the upper-left block to be nonsingular
-- statement:
--   Let $r,s>0$ and take the feasible set $\mathbb R^r\times\mathbb R^s_+$. If the inverse of $T(w)=Aw+N_{\mathbb R^r\times\mathbb R^s_+}(w)$ is a single-valued, globally Lipschitz function defined at every $y\in\mathbb R^{r+s}$, then
--
--   $$
--   \det A_{11}\ne0.
--   $$
--
--   This is the necessity of condition (1) in Theorem 3.1 and rules out a singular upper block even when the lower block is constrained.
-- source:
--   Robinson, Strongly regular generalized equations, Math. Oper. Res. 5 (1980), p. 52, necessity paragraph of proof of Theorem 3.1

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting

namespace RobinsonSR.Schur

/-- Robinson, p. 52, necessity of condition (1). -/
theorem nonsingular_of_inv_lipschitz (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (h : InvIsLipschitzFunction (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)
      (prodSet (nonnegOrthant s))) :
    A₁₁.det ≠ 0 := by sorry

end RobinsonSR.Schur
