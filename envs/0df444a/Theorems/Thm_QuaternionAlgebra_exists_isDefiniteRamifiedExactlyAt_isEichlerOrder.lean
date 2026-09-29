-- Prove2me | Theorems.Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isEichlerOrder
-- name    : QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isEichlerOrder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/48ddc51a-ecba-5d0c-9a34-4e32dd2f420b
-- title:
--   Definite quaternion algebra ramified at q with Eichler order of level N
-- statement:
--   Let $q$ be a prime number and let $N$ be a nonzero natural number with $q \nmid N$. The assertion is that there exist rational numbers $a$ and $b$ such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies [`QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q`](def/QuaternionAlgebra_EichlerOrder.html#L87), that is: $a < 0$, $b < 0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the base change $\mathbb{H}[\mathbb{Q},a,b] \otimes_{\mathbb{Q}} \mathbb{Q}_v$ to the $v$-adic completion has all its nonzero elements invertible precisely when $q$ lies in the prime ideal attached to $v$; and moreover that for such $a,b$ there is a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$ satisfying [`QuaternionAlgebra.IsEichlerOrder Λ N`](def/QuaternionAlgebra_EichlerOrder.html#L69), i.e. there are two submodules $\Lambda_1, \Lambda_2$, each satisfying the predicate `IsOrder` and maximal among such submodules under inclusion, with $\Lambda = \Lambda_1 \sqcap \Lambda_2$ and with the relative index of the additive subgroup of $\Lambda$ inside that of $\Lambda_1$ equal to $N$.
--
--   This is the existence statement for the definite rational quaternion algebra $B_{q,\infty}$, ramified at $q$ and at the archimedean place, together with an Eichler order of level $N$ prime to $q$; the order is the lattice on which the associated Brandt–Eichler Hecke modules are built. It is the starting input of the Čerednik–Drinfeld constructions recorded in the project, which cite it to produce maximal orders acting on the relevant data in characteristic $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_exists_isDefiniteRamifiedExactlyAt_isEichlerOrder.lean

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion

theorem QuaternionAlgebra.exists_isDefiniteRamifiedExactlyAt_isEichlerOrder
    (q : ℕ) (hq : q.Prime) (N : ℕ) (hN : N ≠ 0) (hqN : ¬ q ∣ N) :
    ∃ a b : ℚ, QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q ∧
      ∃ Λ : Submodule ℤ ℍ[ℚ, a, b], QuaternionAlgebra.IsEichlerOrder Λ N := by sorry
