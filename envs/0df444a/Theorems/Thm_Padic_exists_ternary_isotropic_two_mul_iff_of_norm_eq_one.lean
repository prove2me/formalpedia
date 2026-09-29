-- Prove2me | Theorems.Thm_Padic_exists_ternary_isotropic_two_mul_iff_of_norm_eq_one
-- name    : Padic.exists_ternary_isotropic_two_mul_iff_of_norm_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e54457de-f313-56d6-8e4e-0860c3f6a590
-- title:
--   Isotropy of z²-2ax²-by² over ℚ₂ for units a,b
-- statement:
--   Let $a$ and $b$ be elements of the field $\mathbb{Q}_2$ of $2$-adic numbers whose $2$-adic absolute values satisfy $\|a\| = 1$ and $\|b\| = 1$, i.e. both are $2$-adic units. The theorem asserts the equivalence of two conditions. The first is that there exist $z, x, y \in \mathbb{Q}_2$, not all three of them zero (that is, it is not the case that $z = 0$, $x = 0$ and $y = 0$ simultaneously), with $z^2 - (2a)x^2 - by^2 = 0$; thus the ternary quadratic form $z^2 - 2a\,x^2 - b\,y^2$ is isotropic over $\mathbb{Q}_2$. The second is the disjunction $\|b - 1\| \le 2^{-3}$ or $\|2a + b - 1\| \le 2^{-3}$, the bounds being inequalities between real numbers with $2^{-3}$ written as an integer power of $2$; equivalently, $b \equiv 1 \pmod 8$ or $2a + b \equiv 1 \pmod 8$ in $\mathbb{Z}_2$.
--
--   This is the $p = 2$ case of the classical criterion for isotropy of a diagonal ternary form over a $p$-adic field, here for the form $\langle 1, -2a, -b\rangle$ with $a, b$ units, and amounts to the computation of the $2$-adic Hilbert symbol $(2a, b)_2$. It is used in the determination of the local behaviour of the quaternion algebras entering the argument, via [`QuaternionAlgebra.exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem`](thm.html#QuaternionAlgebra.exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem) and [`Rat.hilbertReciprocity_even_card_not_ternary_isotropic`](thm.html#Rat.hilbertReciprocity_even_card_not_ternary_isotropic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_exists_ternary_isotropic_two_mul_iff_of_norm_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Padic.exists_ternary_isotropic_two_mul_iff_of_norm_eq_one (a b : ℚ_[2]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[2], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (2 * a) * x ^ 2 - b * y ^ 2 = 0) ↔
      ‖b - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) ∨ ‖2 * a + b - 1‖ ≤ (2 : ℝ) ^ (-3 : ℤ) := by sorry
