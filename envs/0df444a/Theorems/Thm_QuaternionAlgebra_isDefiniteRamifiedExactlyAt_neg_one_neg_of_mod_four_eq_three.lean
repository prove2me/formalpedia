-- Prove2me | Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three
-- name    : QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/f5e17370-5e67-5ecf-a56e-468dbb6e3ffa
-- title:
--   Definite quaternion algebra (-1,-q) ramified exactly at q
-- statement:
--   Let $q$ be a natural number that is prime and satisfies $q \equiv 3 \pmod 4$. The assertion is that the triple $(-1, -q, q)$ satisfies the predicate [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt`](def/QuaternionAlgebra_EichlerOrder.html#L87), i.e. that the following three statements hold for the rational quaternion algebra $\mathbb{H}[\mathbb{Q}, -1, -q]$ with parameters $a = -1$ and $b = -(q:\mathbb{Q})$: first, $-1 < 0$; second, $-(q:\mathbb{Q}) < 0$; and third, for every $v$ in the height-one spectrum of the ring of integers $\mathcal{O}_{\mathbb{Q}}$, the condition that every nonzero element of the base change $\mathbb{H}[\mathbb{Q}, -1, -q] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ to the $v$-adic completion of $\mathbb{Q}$ is a unit holds if and only if the image of $q$ in $\mathcal{O}_{\mathbb{Q}}$ lies in the prime ideal attached to $v$. Thus the two negativity conditions record definiteness in the form of negative parameters, and the third condition says that the completed algebra is a division algebra precisely at the place dividing $q$.
--
--   This is the congruence class $q \equiv 3 \pmod 4$ of the classical statement that for each prime $q$ there is a definite rational quaternion algebra whose finite ramification set is exactly $\{q\}$, here realised concretely as $\mathbb{H}[\mathbb{Q},-1,-q]$. It is one branch in the case analysis behind [`QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt), which supplies the definite quaternion algebra of prime discriminant used for Eichler orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_of_mod_four_eq_three
    (q : ℕ) (hq : q.Prime) (h3 : q % 4 = 3) :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-1 : ℚ) (-(q : ℚ)) q := by sorry
