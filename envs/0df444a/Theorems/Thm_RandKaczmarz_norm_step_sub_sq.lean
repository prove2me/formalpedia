-- Prove2me | Theorems.Thm_RandKaczmarz_norm_step_sub_sq
-- name    : RandKaczmarz.norm_step_sub_sq
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:15:58.636843+00:00
-- url     : https://prove2.me/theorems/c9971992-93ce-4775-8b02-2e62617c8d3d
-- title:
--   Proof of Theorem 2: the Pythagoras identity for one projection
-- statement:
--   Let $Ax=b$ and let row $i$ satisfy $a_i\ne0$. For every $x_0$,
--   $$\|\mathrm{step}_i(x_0)-x\|_2^2=\|x_0-x\|_2^2-\frac{|\langle a_i,x_0-x\rangle|^2}{\|a_i\|_2^2}.$$
--   This is Pythagoras for one projection, from the proof of Theorem 2. It is an identity, not an inequality.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 5, proof of Theorem 2, the displays $\|x_k-x\|_2^2 = \|x_{k-1}-x\|_2^2 - \|x_{k-1}-x_k\|_2^2$ and $\|x_{k-1}-x_k\|_2 = \langle x_{k-1}-x, Z_k\rangle$

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem norm_step_sub_sq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ)
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) (i : Fin m) (hi : krow A i ≠ 0) :
    ‖step A b i x₀ - x‖ ^ 2
      = ‖x₀ - x‖ ^ 2 - ‖⟪krow A i, x₀ - x⟫_ℂ‖ ^ 2 / ‖krow A i‖ ^ 2 := by sorry

end RandKaczmarz
