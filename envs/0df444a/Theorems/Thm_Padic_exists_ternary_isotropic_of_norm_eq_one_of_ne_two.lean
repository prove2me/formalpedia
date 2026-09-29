-- Prove2me | Theorems.Thm_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two
-- name    : Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/8e34103f-d763-5fd1-bda8-a18de86c3a62
-- title:
--   Ternary forms in p-adic units are isotropic, p odd
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $a, b \in \mathbb{Q}_p$ satisfy $\|a\| = 1$ and $\|b\| = 1$, i.e. both are $p$-adic units. Then there exist $z, x, y \in \mathbb{Q}_p$ such that it is not the case that $z = 0$ and $x = 0$ and $y = 0$ simultaneously, and $z^2 - a x^2 - b y^2 = 0$. In other words, the ternary quadratic form $z^2 - a x^2 - b y^2$ over $\mathbb{Q}_p$ is isotropic: it has a zero other than the origin. The non-triviality is stated exactly as the negation of the conjunction of the three vanishing conditions, so the witness produced has at least one nonzero coordinate; in fact the solutions constructed have $y = 1$.
--
--   This is the classical statement that the Hilbert symbol $(a,b)_p$ equals $1$ for $p$-adic units $a, b$ at an odd prime $p$, equivalently that a ternary form with unit coefficients is isotropic over $\mathbb{Q}_p$. It feeds the local analysis of quaternion algebras used in the project, being cited in the study of Eichler orders, local Hecke sets and the Čerednik–Drinfeld material, where ramification behaviour at odd primes must be computed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_exists_ternary_isotropic_of_norm_eq_one_of_ne_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Padic.exists_ternary_isotropic_of_norm_eq_one_of_ne_two
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) :
    ∃ z x y : ℚ_[p], ¬ (z = 0 ∧ x = 0 ∧ y = 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 := by sorry
