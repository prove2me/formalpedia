-- Prove2me | Theorems.Thm_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one
-- name    : PadicInt.toZModPow_two_pow_eq_one_of_toZMod_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/3a1fbadd-6e73-5414-add3-48e295bce1fe
-- title:
--   p-th powers of principal units lie in 1+p²ℤₚ
-- statement:
--   Let $p$ be a prime number and let $z$ be a $p$-adic integer, $z \in \mathbb{Z}_p$. Assume that the reduction of $z$ under the canonical ring homomorphism $\mathbb{Z}_p \to \mathbb{Z}/p$ (`PadicInt.toZMod`) equals $1$, that is, $z \equiv 1 \pmod{p\mathbb{Z}_p}$. The conclusion is that the image of $z^p$ under the canonical ring homomorphism $\mathbb{Z}_p \to \mathbb{Z}/p^2$ (`PadicInt.toZModPow 2`) equals $1$, i.e. $z^p \equiv 1 \pmod{p^2\mathbb{Z}_p}$. No parity assumption is imposed: the statement covers $p = 2$ as well as odd primes, and it asserts only the inclusion $(1 + p\mathbb{Z}_p)^p \subseteq 1 + p^2\mathbb{Z}_p$, not the reverse inclusion or the equality of these groups.
--
--   This is the elementary half of the description of $p$-th powers of principal units in $\mathbb{Z}_p^\times$: raising to the $p$-th power maps $1 + p\mathbb{Z}_p$ into $1 + p^2\mathbb{Z}_p$. It is used in [`PadicInt.dvd_of_one_add_prime_pow_eq_pow`](thm.html#PadicInt.dvd_of_one_add_prime_pow_eq_pow), where the congruence forces a divisibility condition on exponents, expressing the independence of the principal unit $1 + p$ modulo $p$-th powers.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PadicInt.toZModPow_two_pow_eq_one_of_toZMod_eq_one {p : ℕ} [hp : Fact p.Prime]
    {z : ℤ_[p]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZModPow 2 (z ^ p) = 1 := by sorry
