-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
-- name    : QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/8f26281b-4e50-531c-bcca-5c6616b5a9c8
-- title:
--   Raising the level of an Eichler order by one split prime
-- statement:
--   Let $a,b\in\mathbb Q$ and let $B=\mathbb H[\mathbb Q,a,b]$ be the associated quaternion algebra. Let $q,q'$ be primes with $q'\neq q$, and assume [`QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q'`](def/CerednikDrinfeld_ShimuraCurve.html#L20), i.e. $0<a$ or $0<b$, and for every height one prime $v$ of $\mathcal O_{\mathbb Q}$ the completion $B\otimes_{\mathbb Q}\mathbb Q_v$ is a division ring (every nonzero element is a unit) exactly when $q\in v$ or $q'\in v$. Let $R$ be a $\mathbb Z$-submodule of $B$ and $N$ a natural number such that [`QuaternionAlgebra.IsEichlerOrder R N`](def/QuaternionAlgebra_EichlerOrder.html#L69) holds: there are $\mathbb Z$-submodules $\Lambda_1,\Lambda_2$ of $B$, each an order that is maximal in the sense that any order containing it equals it, with $R=\Lambda_1\cap\Lambda_2$ and with the relative index of $R$ in $\Lambda_1$, as additive subgroups, equal to $N$. Let $\ell$ be a prime with $\ell\neq q$, $\ell\neq q'$ and $\ell\nmid N$. Then there exists a unit $n$ of $B\otimes_{\mathbb Q}\mathbb A_{\mathbb Q}^{\mathrm{fin}}$ such that $R\cap\,$[`Submodule.conjByFiniteIdele R n`](def/Submodule_FiniteAdeleBox.html#L31), the intersection of $R$ with the set of elements of $B$ lying in $n\cdot(\text{the adelic box of }R)\cdot n^{-1}$, is an Eichler order in the same sense, of level $N\ell$.
--
--   This is the level-raising step for Eichler orders in an indefinite rational quaternion algebra ramified exactly at two finite primes: at a prime $\ell$ not dividing the level nor the discriminant one conjugates by a local idele lying in the double coset of $\mathrm{diag}(1,\ell)$ and intersects, lowering the order by exactly one unit of level. It feeds the construction of Eichler orders of prescribed squarefree level inside a given maximal order, used for the Shimura curves of the Čerednik–Drinfel'd comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.IsEichlerOrder.exists_finiteIdele_meetOrder_isEichlerOrder_mul_of_not_dvd_of_isIndefiniteRamifiedExactlyAt
    {a b : ℚ} {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    (hB : QuaternionAlgebra.IsIndefiniteRamifiedExactlyAt a b q q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') (hℓN : ¬ ℓ ∣ N) :
    ∃ n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
      QuaternionAlgebra.IsEichlerOrder (CerednikDrinfeld.meetOrder R n) (N * ℓ) := by sorry
