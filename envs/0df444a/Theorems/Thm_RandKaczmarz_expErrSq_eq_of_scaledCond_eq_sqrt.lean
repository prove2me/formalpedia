-- Prove2me | Theorems.Thm_RandKaczmarz_expErrSq_eq_of_scaledCond_eq_sqrt
-- name    : RandKaczmarz.expErrSq_eq_of_scaledCond_eq_sqrt
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:18:22.198981+00:00
-- url     : https://prove2.me/theorems/3a1e8d4b-c05b-46ff-a118-10ca2c242a30
-- title:
--   Section 3.2: the estimate of Theorem 2 is an equality when $\kappa(A)=\sqrt{n}$
-- statement:
--   Let $A\in\mathbb{C}^{m\times n}$ have full rank, $m\ge n\ge1$, $\kappa(A)=\sqrt n$ (all singular values equal) and $Ax=b$. Then for every $x_0$ and $k$,
--   $$\mathbb{E}\,\|x_k-x\|_2^2=\bigl(1-\kappa(A)^{-2}\bigr)^k\,\|x_0-x\|_2^2 .$$
--   This is §3.2: Theorem 2 is exact here, because eq. (6) holds with equality and every other step of the proof is an identity.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 9, Section 3.2 'The upper estimate is attained', first paragraph

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem expErrSq_eq_of_scaledCond_eq_sqrt {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (hkappa : scaledCond A = Real.sqrt n)
    (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b) (k : ℕ) :
    expErrSq A b x k x₀ = (1 - (scaledCond A ^ 2)⁻¹) ^ k * ‖x₀ - x‖ ^ 2 := by sorry

end RandKaczmarz
