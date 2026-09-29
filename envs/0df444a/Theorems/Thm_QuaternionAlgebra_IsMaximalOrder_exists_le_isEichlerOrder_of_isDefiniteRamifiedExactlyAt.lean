-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/1bb7169b-6c9a-57fd-befe-7406ca6acf29
-- title:
--   Existence of Eichler orders of level N inside a maximal order
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $q$ be a prime number such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q`](def/QuaternionAlgebra_EichlerOrder.html#L87), i.e. $a<0$, $b<0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all its nonzero elements invertible precisely when $q$ lies in the prime ideal attached to $v$. Let $\Lambda_1$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is a maximal order, meaning that $\Lambda_1$ contains $1$, is closed under multiplication, spans $\mathbb{H}[\mathbb{Q},a,b]$ over $\mathbb{Q}$ and is finitely generated, and that any $\mathbb{Z}$-submodule with these four properties which contains $\Lambda_1$ is equal to $\Lambda_1$. Let $N$ be a nonzero natural number not divisible by $q$. The conclusion is that there exists a $\mathbb{Z}$-submodule $\Lambda\subseteq\Lambda_1$ which is an Eichler order of level $N$, that is, for which there are maximal orders $\Lambda_1',\Lambda_2'$ with $\Lambda=\Lambda_1'\cap\Lambda_2'$ and with the relative index of the additive group of $\Lambda$ in that of $\Lambda_1'$ equal to $N$. Note that the index $N$ is taken relative to the witness $\Lambda_1'$ provided by the Eichler condition, which is not asserted to be the given $\Lambda_1$; only the inclusion $\Lambda\subseteq\Lambda_1$ is claimed.
--
--   This is the existence statement for Eichler orders of squarefree-free level $N$ prime to the ramified place inside a prescribed maximal order of a definite rational quaternion algebra ramified exactly at $q$. It is used by [`QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isEichlerOrder`](thm.html#QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isEichlerOrder), which produces the definite quaternion algebra together with an Eichler order of the required level used to realise the relevant Hecke module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsMaximalOrder.exists_le_isEichlerOrder_of_isDefiniteRamifiedExactlyAt
    {a b : ℚ} {q : ℕ} (hq : q.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q)
    {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (h₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) (hN : N ≠ 0) (hqN : ¬ q ∣ N) :
    ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], Λ ≤ Λ₁ ∧ QuaternionAlgebra.IsEichlerOrder Λ N := by sorry
