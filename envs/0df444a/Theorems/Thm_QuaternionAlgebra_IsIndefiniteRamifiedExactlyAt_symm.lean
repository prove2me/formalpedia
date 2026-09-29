-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_symm
-- name    : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/941615ea-1919-5611-8051-a4ea7191a976
-- title:
--   Symmetry of `IsIndefiniteRamifiedExactlyAt` in its two levels
-- statement:
--   Let $a,b \in \mathbb{Q}$ and let $q,q' \in \mathbb{N}$. The hypothesis is that the predicate `IsIndefiniteRamifiedExactlyAt a b q q'` holds, i.e. that (i) $0 < a$ or $0 < b$, and (ii) for every height-one prime $v$ of the ring of integers $\mathcal{O}_{\mathbb{Q}}$, the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ base-changed along $\mathbb{Q} \to \mathbb{Q}_v$, namely $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ with $\mathbb{Q}_v$ the $v$-adic completion, has every nonzero element a unit if and only if the image of $q$ in $\mathcal{O}_{\mathbb{Q}}$ lies in the prime ideal attached to $v$ or the image of $q'$ does. The conclusion is that `IsIndefiniteRamifiedExactlyAt a b q' q` holds, that is, the same two conditions with the roles of $q$ and $q'$ interchanged: the positivity condition $0 < a \vee 0 < b$ is unchanged, and for each $v$ the local division-algebra condition is equivalent to $q' \in v$ or $q \in v$. No primality or distinctness of $q$ and $q'$ is assumed.
--
--   The predicate records that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ is indefinite and that its set of finite ramified places consists exactly of the primes dividing $q$ or $q'$; the statement is the evident symmetry of this condition in the unordered pair $\{q,q'\}$. It is used so that results proved for one ordering of the two levels can be applied in the other, for instance in the construction of elements of a maximal order in [`QuaternionAlgebra.IsMaximalOrder.exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_mem_add_star_eq_and_mul_add_mul_sub_smul_eq_and_star_sub_eq_of_eq_or_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsIndefiniteRamifiedExactlyAt_symm.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion NumberField
open QuaternionAlgebra IsDedekindDomain

theorem QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt.symm {a b : ℚ} {q q' : ℕ}
    (h : IsIndefiniteRamifiedExactlyAt a b q q') : IsIndefiniteRamifiedExactlyAt a b q' q := by sorry
