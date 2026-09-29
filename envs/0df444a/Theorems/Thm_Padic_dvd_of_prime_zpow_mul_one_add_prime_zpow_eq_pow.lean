-- Prove2me | Theorems.Thm_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow
-- name    : Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/5277c685-a461-5900-b178-9a82291908c9
-- title:
--   p-divisibility of exponents in pⁱ(1+p)^j=yᵖ over ℚₚ
-- statement:
--   Let $p$ be a prime number, let $i,j$ be integers and let $y \in \mathbb{Q}_p$. Here $(p : \mathbb{Q}_p)^i$ and $(1+p : \mathbb{Q}_p)^j$ are integer powers in the group of units of $\mathbb{Q}_p$ (the $\mathbb{Q}_p$-valued zero-power convention being the usual one for `zpow`), and $y^p$ is the natural-number power. The hypothesis is the single equation $p^i (1+p)^j = y^p$ in $\mathbb{Q}_p$. The conclusion is the conjunction of two divisibilities of integers: $p \mid i$ and $p \mid j$. Note that the statement does not assume $y \neq 0$; this is automatic, since the left-hand side is a product of powers of the nonzero elements $p$ and $1+p$, and it is not assumed that $y$ is a unit of $\mathbb{Z}_p$, which again follows from the equation. No congruence condition on $p$ is imposed, so the result holds for $p = 2$ and $p = 3$ as well as for larger primes.
--
--   This is the independence half of the description of $\mathbb{Q}_p^\times/(\mathbb{Q}_p^\times)^p$: the classes of the uniformiser $p$ and of the principal unit $1+p$ generate a subgroup isomorphic to $(\mathbb{Z}/p)^2$. It is used in the computation of the index of the $p$-th power subgroup in $\mathbb{Q}_p^\times$, via [`Padic.index_range_powMonoidHom_units_of_ne_two`](thm.html#Padic.index_range_powMonoidHom_units_of_ne_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Padic_dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow {p : ℕ} [hp : Fact p.Prime]
    {i j : ℤ} {y : ℚ_[p]}
    (h : (p : ℚ_[p]) ^ i * (1 + p : ℚ_[p]) ^ j = y ^ p) :
    (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by sorry
