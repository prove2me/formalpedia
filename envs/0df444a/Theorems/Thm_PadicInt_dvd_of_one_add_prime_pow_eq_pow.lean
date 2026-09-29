-- Prove2me | Theorems.Thm_PadicInt_dvd_of_one_add_prime_pow_eq_pow
-- name    : PadicInt.dvd_of_one_add_prime_pow_eq_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/a89b8fd9-2a21-57d4-ad9d-4d6711601feb
-- title:
--   (1+p)^j a p-th power in ℤₚ forces p ∣ j
-- statement:
--   Let $p$ be a prime number, let $j$ be a natural number and let $z$ be an element of the ring $\mathbb{Z}_p$ of $p$-adic integers. Suppose that $(1+p)^j = z^p$ in $\mathbb{Z}_p$, where $1+p$ denotes the sum of the unit and the image of the natural number $p$. The conclusion is that $p$ divides $j$ (as natural numbers). Equivalently: the principal unit $1+p$ generates a subgroup of $\mathbb{Z}_p^\times$ meeting the $p$-th powers only in powers $(1+p)^{pk}$; no exponent $j$ not divisible by $p$ makes $(1+p)^j$ a $p$-th power in $\mathbb{Z}_p$. The statement is uniform in $p$, including $p = 2$, and no hypothesis is placed on $z$ beyond the displayed equation.
--
--   This is the statement that $1+p$ is independent modulo $p$-th powers in the group of principal units of $\mathbb{Z}_p$, i.e. that its class in $\mathbb{Z}_p^\times/(\mathbb{Z}_p^\times)^p$ has exact order $p$. It is used in the proof of [`Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow`](thm.html#Padic.dvd_of_prime_zpow_mul_one_add_prime_zpow_eq_pow), the corresponding statement for products $p^a(1+p)^b$ in $\mathbb{Q}_p^\times$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_dvd_of_one_add_prime_pow_eq_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PadicInt.dvd_of_one_add_prime_pow_eq_pow {p : ℕ} [hp : Fact p.Prime]
    {j : ℕ} {z : ℤ_[p]} (h : (1 + p : ℤ_[p]) ^ j = z ^ p) : p ∣ j := by sorry
