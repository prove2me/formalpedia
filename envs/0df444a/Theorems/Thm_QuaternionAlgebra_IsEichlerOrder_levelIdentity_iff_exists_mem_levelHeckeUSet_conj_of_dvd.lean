-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd
-- name    : QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/2e471120-e502-5a41-837c-9ee7db3ad794
-- title:
--   Level identity at ℓ ∣ N versus idelic Hecke membership of wtw⁻¹
-- statement:
--   Let $N$ be a nonzero natural number and $q,q'$ primes with $q\nmid N$, $q'\nmid N$ and $q'\neq q$, and let $a,b\in\mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt`, i.e. $0<a$ or $0<b$, and for every finite place $v$ of $\mathbb{Q}$ the completion $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra precisely when $v$ lies above $q$ or $q'$. Let $\Lambda$ be a maximal order (an order maximal among orders containing it), $N$ squarefree, and $R\leq\Lambda$ an Eichler order of level $N$, i.e. an intersection of two maximal orders with relative index $N$ in the first. Let $J'$ be a $\mathbb{Z}$-submodule with: $\Lambda\leq J'$; $J'$ stable under left multiplication by $\Lambda$; $N\cdot J'\subseteq\Lambda$; relative index $N^2$ of $\Lambda$ in $J'$; and $x\in\Lambda$ lies in $R$ exactly when $J'x\subseteq J'$. Let $w$ be a unit of the algebra lying in $R$ with $\mathrm{nrd}(w)=N$ and with $x\in R\iff wxw^{-1}\in R$ for all $x$, let $\ell$ be a prime dividing $N$, and let $t\in R$ with $\mathrm{nrd}(t)=\ell$. Then the identity $\ell J'+\Lambda t=J't$ (as sets of elements, stated pointwise) holds if and only if there exists $h\in$ `levelHeckeUSet` $\Lambda\,R\,\ell$ whose underlying element of $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{A}_{\mathbb{Q}}^{\mathrm{fin}}$ equals $(wtw^{-1})\otimes 1$; here `levelHeckeUSet` consists of those finite-idelic units $h$ lying in `primeHeckeSet` $R\,\ell$ (an $\ell$-primitivity condition on $h$ and $h^{-1}$ relative to the adelic box of $R$) for which conjugation by $h$ moves $R$ and does not carry $\Lambda$ to a submodule containing $R$.
--
--   This is the dictionary translating the local, integral "level identity" $\ell J'+\Lambda t=J't$ for a norm-$\ell$ element $t$ of an Eichler order of squarefree level $N$ into membership of the Atkin–Lehner conjugate $wtw^{-1}$ in the idelic Hecke set used to build the Čerednik–Drinfel'd class-set graph. It is used in the construction of the Atkin–Lehner/Hecke correspondence on the level module, feeding [`QuaternionAlgebra.IsEichlerOrder.exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_CerednikDrinfeld_ClassSetGraph

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion TensorProduct NumberField MatrixGroups Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.levelIdentity_iff_exists_mem_levelHeckeUSet_conj_of_dvd
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (w : (ℍ[ℚ, a, b])ˣ) (hwR : (w : ℍ[ℚ, a, b]) ∈ R) (hwn : nrd (w : ℍ[ℚ, a, b]) = (N : ℚ))
    (hwnorm : ∀ x : ℍ[ℚ, a, b], x ∈ R ↔ (w : ℍ[ℚ, a, b]) * x * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N) (t : ℍ[ℚ, a, b]) (ht : t ∈ R) (hnt : nrd t = (ℓ : ℚ)) :
    (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) ↔
      ∃ h ∈ levelHeckeUSet Λ R ℓ,
        (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = ((w : ℍ[ℚ, a, b]) * t * ((w⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by sorry
