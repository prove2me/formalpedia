-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/0825b007-1ccb-5478-8254-a1d2104e3d14
-- title:
--   Existence of a definite rational quaternion algebra ramified exactly at q
-- statement:
--   Let $q$ be a natural number and assume $q$ is prime. Then there exist rational numbers $a$ and $b$ satisfying [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q`](def/QuaternionAlgebra_EichlerOrder.html#L87), that is: $a<0$, $b<0$, and for every $v$ in the height-one spectrum of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ of $\mathbb{Q}$, the following two conditions are equivalent — (i) every nonzero element of the $v$-adic base change $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}} \mathbb{Q}_v$ of the quaternion algebra with parameters $a,b$ is a unit, where $\mathbb{Q}_v$ denotes the adic completion of $\mathbb{Q}$ at $v$; and (ii) the image of $q$ in $\mathcal{O}_{\mathbb{Q}}$ lies in the prime ideal attached to $v$. Thus the quaternion algebra $\left(\frac{a,b}{\mathbb{Q}}\right)$ is definite (both structure constants being negative) and, among the finite places, its completion is a division algebra precisely at the place above $q$.
--
--   This is the existence of a definite rational quaternion algebra of prime discriminant $q$, the starting point for the quaternionic constructions on the Taylor–Wiles side of the argument. It is used by [`QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isEichlerOrder`](thm.html#QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isEichlerOrder), which upgrades the conclusion by producing in addition an Eichler order in such an algebra.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt (q : ℕ) (hq : q.Prime) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q := by sorry
