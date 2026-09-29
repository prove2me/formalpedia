-- Prove2me | Theorems.Thm_RandKaczmarz_sum_inner_krow_sq_lower
-- name    : RandKaczmarz.sum_inner_krow_sq_lower
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:14:41.651759+00:00
-- url     : https://prove2.me/theorems/47c78fe1-9c08-49c0-8b03-f19e7854425b
-- title:
--   Equation (6): $\sum_{j} |\langle z, a_j \rangle|^2 \ge \|z\|_2^2 / \|A^{-1}\|_2^2$
-- statement:
--   For every $z\in\mathbb{C}^n$,
--   $$\sum_{j=1}^m|\langle a_j,z\rangle|^2\ge\sigma_{\min}(A)^2\,\|z\|_2^2 .$$
--   This is eq. (6). The left-hand side is $\|Az\|_2^2$, so the inequality restates the definition of $\sigma_{\min}$ over the rows. No rank hypothesis is needed.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 4, eq. (6)

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem sum_inner_krow_sq_lower {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (z : EuclideanSpace ℂ (Fin n)) :
    sigmaMin A ^ 2 * ‖z‖ ^ 2 ≤ ∑ j, ‖⟪krow A j, z⟫_ℂ‖ ^ 2 := by sorry

end RandKaczmarz
