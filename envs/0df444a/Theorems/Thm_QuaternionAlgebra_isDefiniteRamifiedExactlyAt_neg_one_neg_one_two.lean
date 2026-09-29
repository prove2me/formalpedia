-- Prove2me | Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two
-- name    : QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_one_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/65d723c9-2494-51dd-92e7-b947f35df1b5
-- title:
--   Hamilton quaternions over ℚ: definite, ramified exactly at 2
-- statement:
--   The assertion is [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-1 : ℚ) (-1) 2`](def/QuaternionAlgebra_EichlerOrder.html#L87), which unfolds to three statements about the quaternion algebra $\mathbb{H}[\mathbb{Q},-1,-1]$ with $i^2=j^2=-1$: first, $-1<0$; second, $-1<0$; and third, for every height-one prime $v$ of the ring of integers $\mathcal{O}_{\mathbb{Q}}$ of $\mathbb{Q}$, the condition that every nonzero element of the base change $\mathbb{H}[\mathbb{Q},-1,-1]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ (the tensor product with the $v$-adic completion of $\mathbb{Q}$) is a unit holds if and only if the image of $2$ in $\mathcal{O}_{\mathbb{Q}}$ lies in the prime ideal of $v$. Thus the two defining parameters are negative, so the algebra is definite, and its completion at a finite place is a division algebra precisely at the place above $2$: the non-$2$-adic completions carry zero divisors, while at the place above $2$ every nonzero element is invertible. No hypotheses are assumed; the statement concerns the single rational quaternion algebra with parameters $(-1,-1)$ and the integer $q=2$.
--
--   This identifies the Hamilton quaternions as a definite rational quaternion algebra whose finite ramification locus is exactly $\{2\}$, i.e. the case $q=2$ of the existence of a definite quaternion algebra over $\mathbb{Q}$ ramified exactly at one prime (together with the archimedean place). It is used by [`QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt), which supplies such an algebra for each prime $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_neg_one_neg_one_two.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_neg_one_neg_one_two :
    QuaternionAlgebra.IsDefiniteRamifiedExactlyAt (-1 : ℚ) (-1) 2 := by sorry
