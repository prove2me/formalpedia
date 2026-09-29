-- Prove2me | Theorems.Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/bc7d4b81-d925-5af9-89f2-33d670051080
-- title:
--   Multiplicativity in the second slot of the ramification data
-- statement:
--   Let $r$ and $\bar r$ be primes with $\bar r \neq r$, and let $t, s, c' \in \mathbb{Q}$. Here a quaternion algebra $\mathbb{H}[\mathbb{Q}, a, b]$ is said to be ramified at a finite place, i.e. at a height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$, when every nonzero element of $\mathbb{H}[\mathbb{Q}, a, b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit. Assume `IsIndefiniteRamifiedExactlyAt t s r rbar`, that is: $0 < t$ or $0 < s$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ the algebra $\mathbb{H}[\mathbb{Q}, t, s] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible precisely when $r \in v$ or $\bar r \in v$. Assume also `IsDefiniteRamifiedExactlyAt t c' r`, that is: $t < 0$, $c' < 0$, and for every such $v$ the algebra $\mathbb{H}[\mathbb{Q}, t, c'] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ has all its nonzero elements invertible precisely when $r \in v$. The conclusion is `IsDefiniteRamifiedExactlyAt t (s * c') rbar`: one has $t < 0$ and $s c' < 0$, and for every height-one prime $v$ of $\mathcal{O}_{\mathbb{Q}}$ every nonzero element of $\mathbb{H}[\mathbb{Q}, t, s c'] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ is a unit if and only if $\bar r \in v$.
--
--   This is the multiplicativity of the Hilbert symbol $(t, \cdot)_v$ in its second argument, combined with Hilbert reciprocity and a sign count, in the concrete form needed to pass from an indefinite rational quaternion algebra ramified exactly at $r$ and $\bar r$, together with a definite one ramified exactly at $r$, to a definite one ramified exactly at $\bar r$. It is used in the construction of the quaternionic data underlying the Čerednik–Drinfeld description of the relevant Shimura curve, being cited by [`QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt`](thm.html#QuaternionAlgebra.exists_algHom_matrix_apply_mem_and_trace_and_forall_iff_mem_range_of_isIndefiniteRamifiedExactlyAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.isDefiniteRamifiedExactlyAt_mul_of_isIndefiniteRamifiedExactlyAt_of_isDefiniteRamifiedExactlyAt
    {r rbar : ℕ} [Fact r.Prime] [Fact rbar.Prime] (hrr : rbar ≠ r)
    {t s c' : ℚ} (hB : IsIndefiniteRamifiedExactlyAt t s r rbar)
    (hH' : IsDefiniteRamifiedExactlyAt t c' r) :
    IsDefiniteRamifiedExactlyAt t (s * c') rbar := by sorry
