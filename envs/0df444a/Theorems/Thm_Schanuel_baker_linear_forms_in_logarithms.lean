-- Prove2me | Theorems.Thm_Schanuel_baker_linear_forms_in_logarithms
-- name    : Schanuel.baker_linear_forms_in_logarithms
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T17:33:47.248724+00:00
-- url     : https://prove2.me/theorems/a0417130-5d91-4638-a293-bea5fb28fcf6
-- title:
--   Baker's theorem on linear forms in logarithms
-- statement:
--   **Baker's theorem.** Let $\lambda_1, \dots, \lambda_n$ be logarithms of algebraic numbers, that is, complex numbers with $e^{\lambda_i}$ algebraic, and assume they are linearly independent over $\mathbb{Q}$. Let $\beta_0, \beta_1, \dots, \beta_n$ be algebraic numbers, not all zero. Then
--
--   $$\beta_0 + \sum_{i=1}^{n} \beta_i \lambda_i \;\neq\; 0 .$$
--
--   Equivalently, $1, \lambda_1, \dots, \lambda_n$ are linearly independent over the field of algebraic numbers. Baker proved this in 1966, generalizing Gelfond–Schneider from $n = 1$ to arbitrary $n$ and adding the inhomogeneous term $\beta_0$; the effective versions of the theorem underlie the resolution of many Diophantine equations.
-- source:
--   A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204–216, https://doi.org/10.1112/S0025579300003971; see also A. Baker, Transcendental Number Theory, CUP, 1975, Theorem 2.1 and Chapter 2

import Mathlib

namespace Schanuel
theorem baker_linear_forms_in_logarithms (n : ℕ) (l : Fin n → ℂ)
    (hl : LinearIndependent ℚ l) (hlalg : ∀ i, IsAlgebraic ℚ (Complex.exp (l i)))
    (b₀ : ℂ) (b : Fin n → ℂ) (hb₀ : IsAlgebraic ℚ b₀) (hb : ∀ i, IsAlgebraic ℚ (b i))
    (hne : b₀ ≠ 0 ∨ ∃ i, b i ≠ 0) :
    b₀ + ∑ i, b i * l i ≠ 0 := by sorry
end Schanuel
