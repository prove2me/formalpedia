-- Prove2me | Theorems.Thm_RandKaczmarz_expErrSq_le_of_iterations
-- name    : RandKaczmarz.expErrSq_le_of_iterations
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-25T16:17:54.01574+00:00
-- url     : https://prove2.me/theorems/e5415614-49dd-40bf-ac83-c511fb2b13c5
-- title:
--   Section 2.1: $2\log\varepsilon/\log(1-\kappa(A)^{-2})$ iterations suffice for relative accuracy $\varepsilon$
-- statement:
--   Let $A\in\mathbb{C}^{m\times n}$ have full rank, $m\ge n\ge1$, $\kappa(A)>1$, $Ax=b$ and $0<\varepsilon<1$. If
--   $$k\ge\frac{2\log\varepsilon}{\log(1-\kappa(A)^{-2})},$$
--   then $\mathbb{E}\|x_k-x\|_2^2\le\varepsilon^2\|x_0-x\|_2^2$. This is §2.1, eqs. (10)–(11).
--
--   **Formalization Note** The hypothesis $\kappa(A)>1$ makes the logarithm finite and negative; it holds whenever $n\ge2$. The asymptotic form $\approx2\kappa(A)^2\log(1/\varepsilon)$ is not formalized.
-- source:
--   Strohmer & Vershynin, A randomized Kaczmarz algorithm with exponential convergence, arXiv:math/0702226v1 [math.NA], https://arxiv.org/abs/math/0702226 (published: J. Fourier Anal. Appl. 15 (2009), 262-278), p. 6, Section 2.1 'Quadratic time', eq. (10) and the first bound of eq. (11)

import Definitions.Def_RandKaczmarz_core

open scoped InnerProductSpace ComplexConjugate
open WithLp Matrix

namespace RandKaczmarz

theorem expErrSq_le_of_iterations {m n : ℕ} (hn : 0 < n) (hmn : n ≤ m)
    (A : Matrix (Fin m) (Fin n) ℂ) (b : Fin m → ℂ) (hA : Function.Injective (mulVecE A))
    (hkappa : 1 < scaledCond A) (x x₀ : EuclideanSpace ℂ (Fin n)) (hx : A *ᵥ ofLp x = b)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (k : ℕ)
    (hk : 2 * Real.log ε / Real.log (1 - (scaledCond A ^ 2)⁻¹) ≤ (k : ℝ)) :
    expErrSq A b x k x₀ ≤ ε ^ 2 * ‖x₀ - x‖ ^ 2 := by sorry

end RandKaczmarz
