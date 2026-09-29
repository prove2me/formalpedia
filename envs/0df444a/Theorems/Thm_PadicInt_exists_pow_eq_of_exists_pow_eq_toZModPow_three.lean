-- Prove2me | Theorems.Thm_PadicInt_exists_pow_eq_of_exists_pow_eq_toZModPow_three
-- name    : PadicInt.exists_pow_eq_of_exists_pow_eq_toZModPow_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:59.592692+00:00
-- url     : https://prove2.me/theorems/fd80292d-5353-50ab-904b-4767d2801127
-- title:
--   Units of ℤₚ: p-th powers mod p³ lift
-- statement:
--   Let $p$ be a prime and let $u$ be an element of the ring $\mathbb{Z}_p$ of $p$-adic integers whose $p$-adic norm $\|u\|$ equals $1$, that is, $u$ is a unit. Assume further that the image of $u$ in $\mathbb{Z}/p^3\mathbb{Z}$ under the reduction map `PadicInt.toZModPow 3` is a $p$-th power: there exists $c \in \mathbb{Z}/p^{3}\mathbb{Z}$ with $c^{p} = u \bmod p^{3}$. Then $u$ is a $p$-th power in $\mathbb{Z}_p$: there exists $z \in \mathbb{Z}_p$ with $z^{p} = u$. Only one implication is asserted; the converse (that a $p$-th power in $\mathbb{Z}_p$ reduces to a $p$-th power modulo $p^{3}$) is trivial and is not part of this statement. No exactness or uniqueness of the root $z$ is claimed, although the root produced is in fact the unique one in the residue disc of a lift of $c$.
--
--   This is the lifting half of the description of $\mathbb{Z}_p^{\times}/(\mathbb{Z}_p^{\times})^{p}$ at the wild place, reducing the property of being a $p$-th power to a congruence condition modulo $p^{3}$; being a $p$-th power modulo $p^{2}$ alone would not suffice, since the derivative of $X^{p}-u$ is divisible by $p$. It is used in the computation of local units modulo $p$-th powers at $\ell = p$, and is cited by [`PadicInt.exists_pow_eq_of_toZModPow_two_eq_one`](thm.html#PadicInt.exists_pow_eq_of_toZModPow_two_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PadicInt_exists_pow_eq_of_exists_pow_eq_toZModPow_three.lean

import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.FieldTheory.Finite.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem PadicInt.exists_pow_eq_of_exists_pow_eq_toZModPow_three {p : ℕ} [hp : Fact p.Prime] {u : ℤ_[p]} (hu : ‖u‖ = 1) (hres : ∃ c : ZMod (p ^ 3), c ^ p = PadicInt.toZModPow 3 u) :
    ∃ z : ℤ_[p], z ^ p = u := by sorry
