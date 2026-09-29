-- Prove2me | Theorems.Thm_Schanuel_lindemann_weierstrass
-- name    : Schanuel.lindemann_weierstrass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T17:31:35.236603+00:00
-- url     : https://prove2.me/theorems/afb75b5a-3ca6-4700-9c55-ebd4e3ecc762
-- title:
--   Lindemann–Weierstrass theorem
-- statement:
--   **Lindemann–Weierstrass theorem.** Let $\alpha_1, \dots, \alpha_n$ be pairwise distinct algebraic numbers and let $\beta_1, \dots, \beta_n$ be algebraic numbers, not all zero. Then
--
--   $$\sum_{i=1}^{n} \beta_i e^{\alpha_i} \neq 0 .$$
--
--   Equivalently, the numbers $e^{\alpha_1}, \dots, e^{\alpha_n}$ are linearly independent over the field $\overline{\mathbb{Q}}$ of algebraic numbers. Taking $n = 2$, $\alpha_1 = \alpha$, $\alpha_2 = 0$ recovers the Hermite–Lindemann theorem.
-- source:
--   K. Weierstrass, Zu Lindemann's Abhandlung 'Über die Ludolph'sche Zahl', Sitzungsber. Preuss. Akad. Wiss. (1885), 1067–1085; see also A. Baker, Transcendental Number Theory, CUP, 1975, Theorem 1.4

import Mathlib

namespace Schanuel
theorem lindemann_weierstrass (n : ℕ) (a b : Fin n → ℂ)
    (ha : ∀ i, IsAlgebraic ℚ (a i)) (hainj : Function.Injective a)
    (hb : ∀ i, IsAlgebraic ℚ (b i)) (hb0 : ∃ i, b i ≠ 0) :
    ∑ i, b i * Complex.exp (a i) ≠ 0 := by sorry
end Schanuel
