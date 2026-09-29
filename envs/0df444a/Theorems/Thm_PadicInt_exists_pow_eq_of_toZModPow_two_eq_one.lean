-- Prove2me | Theorems.Thm_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one
-- name    : PadicInt.exists_pow_eq_of_toZModPow_two_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/06a8de6f-63b5-5e09-b1d1-ecbc54d96143
-- title:
--   Units congruent to 1 mod p² are p-th powers of principal units
-- statement:
--   Let $p$ be a prime, assumed different from $2$, and let $u$ be a $p$-adic integer in $\mathbb{Z}_p$ whose image under the reduction map `PadicInt.toZModPow 2` to $\mathbb{Z}/p^2$ equals $1$, i.e. $u \equiv 1 \pmod{p^2}$. The assertion is that there exists $z \in \mathbb{Z}_p$ whose image under `PadicInt.toZMod` in $\mathbb{Z}/p$ equals $1$, so $z \equiv 1 \pmod p$, and such that $z^p = u$ exactly in $\mathbb{Z}_p$. Thus every unit congruent to $1$ modulo $p^2$ is the $p$-th power of a principal unit, the extracted root being produced together with the congruence $z \equiv 1 \pmod p$ rather than merely its existence as a $p$-th root.
--
--   This is the inclusion $1 + p^2\mathbb{Z}_p \subseteq (1 + p\mathbb{Z}_p)^p$ for odd $p$, the wild part of the structure theorem $1 + p\mathbb{Z}_p \cong \mathbb{Z}_p$ for the principal units of $\mathbb{Z}_p$. It is used by [`PadicInt.exists_eq_one_add_prime_pow_mul_pow`](thm.html#PadicInt.exists_eq_one_add_prime_pow_mul_pow) in the analysis of $p$-th power classes of $p$-adic units.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem PadicInt.exists_pow_eq_of_toZModPow_two_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {u : ℤ_[p]} (hu : PadicInt.toZModPow 2 u = 1) :
    ∃ z : ℤ_[p], PadicInt.toZMod z = 1 ∧ z ^ p = u := by sorry
