-- Prove2me | Theorems.Thm_RandKaczmarz_expected_inner_krow_sq_lower
-- name    : RandKaczmarz.expected_inner_krow_sq_lower
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:15:25.230654+00:00
-- url     : https://prove2.me/theorems/0cef1f11-3e84-4967-998d-d28e3dc72dc9
-- title:
--   Equations (7) and (9): $\mathbb{E}|\langle z, Z \rangle|^2 \ge \kappa(A)^{-2}\|z\|_2^2$
-- statement:
--   Let $A\in\mathbb{C}^{m\times n}$ have full rank, $m\ge n\ge1$. For every $z\in\mathbb{C}^n$,
--   $$\sum_{j=1}^m p_j\,\Bigl|\Bigl\langle \tfrac{a_j}{\|a_j\|_2},z\Bigr\rangle\Bigr|^2\ge\kappa(A)^{-2}\,\|z\|_2^2 .$$
--   These are eqs. (7) and (9). If $Z=a_j/\|a_j\|_2$ is drawn with probability $p_j$, this says $\mathbb{E}|\langle Z,z\rangle|^2\ge\kappa(A)^{-2}\|z\|_2^2$. It is the key step of the proof.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 4, eq. (7) and p. 5, eq. (8)-(9)

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem expected_inner_krow_sq_lower {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (hA : Function.Injective (mulVecE A))
    (z : EuclideanSpace ℂ (Fin n)) :
    (scaledCond A ^ 2)⁻¹ * ‖z‖ ^ 2
      ≤ ∑ j, rowProb A j * (‖⟪krow A j, z⟫_ℂ‖ ^ 2 / ‖krow A j‖ ^ 2) := by sorry

end RandKaczmarz
