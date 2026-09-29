-- Prove2me | Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five
-- name    : QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/d5dbb967-5a16-5bda-9652-4a223ae38fdd
-- title:
--   The quaternion algebra (-2,-q) over ℚ for q≡ 5 (mod 8)
-- statement:
--   Let $q$ be a prime natural number with $q \equiv 5 \pmod 8$. Then the triple $(-2, -q, q)$ satisfies the project predicate [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt`](def/QuaternionAlgebra_EichlerOrder.html#L87), i.e. three things hold: first, $-2 < 0$ in $\mathbb{Q}$; second, $-q < 0$ in $\mathbb{Q}$; and third, for every $v$ in the height one spectrum of the ring of integers $\mathcal{O}_{\mathbb{Q}}$, the condition that every nonzero element of $\mathbb{H}[\mathbb{Q}, -2, -q] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ (the base change of the rational quaternion algebra with parameters $-2$ and $-q$ along $\mathbb{Q} \to$ the adic completion of $\mathbb{Q}$ at $v$) is a unit is equivalent to the membership $q \in v$, i.e. to $v$ being the prime of $\mathcal{O}_{\mathbb{Q}}$ above $q$. Thus the quaternary norm form of $\mathbb{H}[\mathbb{Q},-2,-q]$ has negative parameters, and the completed algebra is a division algebra at exactly the finite place $q$; nothing is asserted about the archimedean place beyond the sign conditions $-2 < 0$ and $-q < 0$.
--
--   This computes the ramification set of the definite rational quaternion algebra $(-2,-q)$ for $q \equiv 5 \pmod 8$, showing that among the finite places it is ramified exactly at $q$. It is one of the congruence cases used by [`QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt) to produce, for each prime $q$, a definite quaternion algebra over $\mathbb{Q}$ ramified exactly at the finite place $q$ (and at infinity), the algebra whose Eichler orders support the quaternionic side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_two_neg_of_mod_eight_eq_five
    (q : ℕ) (hq : q.Prime) (h5 : q % 8 = 5) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-2 : ℚ) (-(q : ℚ)) q := by sorry
