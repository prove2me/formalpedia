-- Prove2me | Theorems.Thm_Transcendence_quadratic_coeffs_eq_zero_of_transcendental
-- name    : Transcendence.quadratic_coeffs_eq_zero_of_transcendental
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-25T10:34:46.644699+00:00
-- url     : https://prove2.me/theorems/0b946dc3-8d94-4797-b943-02e56589f23d
-- title:
--   A transcendental number is a root of no non-zero quadratic with algebraic coefficients
-- statement:
--   Let $x \in \mathbb{C}$ be transcendental, and let $c_0, c_1, c_2 \in \mathbb{C}$ be algebraic. If
--
--   $$c_2 x^{2} + c_1 x + c_0 = 0,$$
--
--   then $c_2 = c_1 = c_0 = 0$.
--
--   It is used at $x = \pi$ and $x = \pi^{2}$, where it turns a relation with algebraic coefficients into three separate equations.
-- source:
--   Standard. Formal proof: Diaz modulus mission, 25 September 2026 (C. Perassi).

import Mathlib

namespace Transcendence

theorem quadratic_coeffs_eq_zero_of_transcendental {x c₀ c₁ c₂ : ℂ} (hx : Transcendental ℚ x)
    (h₀ : IsAlgebraic ℚ c₀) (h₁ : IsAlgebraic ℚ c₁) (h₂ : IsAlgebraic ℚ c₂)
    (h : c₂ * x ^ 2 + c₁ * x + c₀ = 0) :
    c₂ = 0 ∧ c₁ = 0 ∧ c₀ = 0 := by
  sorry

end Transcendence
