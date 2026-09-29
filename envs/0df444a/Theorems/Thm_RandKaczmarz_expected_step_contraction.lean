-- Prove2me | Theorems.Thm_RandKaczmarz_expected_step_contraction
-- name    : RandKaczmarz.expected_step_contraction
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:16:29.846336+00:00
-- url     : https://prove2.me/theorems/3cf4ae28-d920-4eba-8e50-37a83e2c1bec
-- title:
--   Proof of Theorem 2: one step contracts the expected squared error by $1-\kappa(A)^{-2}$
-- statement:
--   Let $A\in\mathbb{C}^{m\times n}$ have full rank, $m\ge n\ge1$, and $Ax=b$. For every $x_0$,
--   $$\sum_{i=1}^m p_i\,\|\mathrm{step}_i(x_0)-x\|_2^2\le\bigl(1-\kappa(A)^{-2}\bigr)\|x_0-x\|_2^2 .$$
--   One step contracts the expected squared error (proof of Theorem 2). A single step need not contract; only the average does.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 5, proof of Theorem 2, the conditional-expectation display and the line 'By (9) and the independence'

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem expected_step_contraction {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) :
    ∑ i, rowProb A i * ‖step A b i x₀ - x‖ ^ 2
      ≤ (1 - (scaledCond A ^ 2)⁻¹) * ‖x₀ - x‖ ^ 2 := by sorry

end RandKaczmarz
