-- Prove2me | Theorems.Thm_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
-- name    : Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/e4ef7b3b-f389-5127-b8e3-c3c1c246f3b5
-- title:
--   Isotropy of z²-pax²-by² over ℚₚ, p odd
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $a, b \in \mathbb{Q}_p$ be elements of $p$-adic absolute value one, i.e. $\|a\| = \|b\| = 1$, so that $a$ and $b$ are units of $\mathbb{Z}_p$. The assertion is an equivalence. On one side: there exist $z, x, y \in \mathbb{Q}_p$ for which it is not the case that all three of $z = 0$, $x = 0$, $y = 0$ hold simultaneously, and such that $z^2 - (p a) x^2 - b y^2 = 0$; that is, the ternary quadratic form $z^2 - p a x^2 - b y^2$ over $\mathbb{Q}_p$ has a nontrivial zero. On the other side: $b$ is a square in $\mathbb{Q}_p$, in the sense of Mathlib's `IsSquare`, namely $b = r \cdot r$ for some $r \in \mathbb{Q}_p$. Note that the normalisation hypothesis on $a$ enters only through the statement's hypotheses; no integrality is imposed on $z$, $x$, $y$ themselves.
--
--   This is the case $\alpha = 1$, $\beta = 0$ of the classical evaluation of the Hilbert symbol at an odd prime, $(p^{\alpha}u, p^{\beta}v)_p = (-1)^{\alpha\beta\varepsilon(p)}(u/p)^{\beta}(v/p)^{\alpha}$, recast as an isotropy criterion for a ternary form: $(pa, b)_p = 1$ exactly when the unit $b$ is a $p$-adic square. It is used in the determination of the local invariants of an indefinite quaternion algebra, in [`QuaternionAlgebra.exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem`](thm.html#QuaternionAlgebra.exists_indefinite_forall_isUnit_adicCompletion_iff_mem_or_mem), and in the Hilbert reciprocity input [`Rat.hilbertReciprocity_even_card_not_ternary_isotropic`](thm.html#Rat.hilbertReciprocity_even_card_not_ternary_isotropic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Padic.exists_ternary_isotropic_prime_mul_iff_isSquare_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    (∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧
        z ^ 2 - (p * a) * x ^ 2 - b * y ^ 2 = 0) ↔ IsSquare b := by sorry
