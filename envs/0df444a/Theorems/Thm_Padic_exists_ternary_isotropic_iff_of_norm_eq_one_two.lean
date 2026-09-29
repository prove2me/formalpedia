-- Prove2me | Theorems.Thm_Padic_exists_ternary_isotropic_iff_of_norm_eq_one_two
-- name    : Padic.exists_ternary_isotropic_iff_of_norm_eq_one_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/1dd3da61-19c5-58df-80fa-56ae24045433
-- title:
--   Isotropy of z²-ax²-by² over ℚ₂ for units a,b
-- statement:
--   Let $a, b \in \mathbb{Q}_2$ satisfy $\|a\| = \|b\| = 1$, i.e. both are $2$-adic units (their $2$-adic valuation is $0$). The theorem asserts the equivalence of two conditions. The first is that there exist $z, x, y \in \mathbb{Q}_2$, not all three of which vanish (the negation of the conjunction $z = 0 \wedge x = 0 \wedge y = 0$), with $z^2 - a x^2 - b y^2 = 0$; that is, the ternary quadratic form $z^2 - a x^2 - b y^2$ is isotropic over $\mathbb{Q}_2$. The second is the disjunction $\|a - 1\| \le 2^{-2}$ or $\|b - 1\| \le 2^{-2}$, the bounds being on the real $2$-adic absolute value, so that the condition says that $a \equiv 1 \pmod{4}$ or $b \equiv 1 \pmod{4}$ in $\mathbb{Z}_2$. Note that the nontriviality hypothesis is stated as the negation of a conjunction, so it merely excludes the zero vector, and no primitivity is required.
--
--   This is the computation of the Hilbert symbol $(a,b)_2$ for $2$-adic units, equivalently the case $p = 2$ with $a, b$ units of the local solubility criterion for ternary forms: $(a,b)_2 = (-1)^{\varepsilon(a)\varepsilon(b)}$ with $\varepsilon(u) \equiv (u-1)/2 \bmod 2$. It feeds the local analysis of quaternion algebras over $\mathbb{Q}$ at the prime $2$, and is used in the identification of Hecke sets and local orders for Eichler orders in definite quaternion algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_exists_ternary_isotropic_iff_of_norm_eq_one_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Padic.exists_ternary_isotropic_iff_of_norm_eq_one_two (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0) ↔
      ‖a - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) ∨ ‖b - 1‖ ≤ (2 : ℝ) ^ (-2 : ℤ) := by sorry
