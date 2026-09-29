-- Prove2me | Theorems.Thm_RandKaczmarz_sqrt_card_le_scaledCond
-- name    : RandKaczmarz.sqrt_card_le_scaledCond
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:14:20.668985+00:00
-- url     : https://prove2.me/theorems/82efaee7-5eb0-4f92-8e48-2d3ad10da65c
-- title:
--   Equation (3): $\sqrt{n} \le \kappa(A)$
-- statement:
--   Let $A\in\mathbb{C}^{m\times n}$ have full rank, $m\ge n\ge1$. Then
--   $$\sqrt n\le\kappa(A).$$
--   This is the left half of eq. (3). It puts the contraction factor $1-\kappa(A)^{-2}$ in $[0,1)$.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 3, eq. (3), left-hand inequality $1 \le \kappa(A)/\sqrt{n}$

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem sqrt_card_le_scaledCond {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : Function.Injective (mulVecE A)) :
    Real.sqrt n ≤ scaledCond A := by sorry

end RandKaczmarz
