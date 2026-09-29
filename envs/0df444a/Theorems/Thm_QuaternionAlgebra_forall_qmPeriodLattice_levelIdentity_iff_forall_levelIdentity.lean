-- Prove2me | Theorems.Thm_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity
-- name    : QuaternionAlgebra.forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/cc10e5d8-00e1-5147-91cd-c123c2c62c47
-- title:
--   Pulling the level identity back along the period map
-- statement:
--   Fix primes $q$ and $q'$ and rationals $a,b$, and assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. that $a>0$ or $b>0$ and that for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\iota : \mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra homomorphism, let $\Lambda, J'$ be $\mathbb{Z}$-submodules of $\mathbb{H}[\mathbb{Q},a,b]$, let $t$ be a quaternion, $\ell$ a natural number and $\tau$ a point of the upper half plane. Write $\mathrm{per}_\tau(x) = \iota(x)\cdot{}^{t}(\tau,1) \in \mathbb{C}^2$, the matrix $\iota(x)$ being viewed over $\mathbb{C}$, and let `qmPeriodLattice` $\iota\,J'\,\tau$ be the image $\mathrm{per}_\tau(J')$. The assertion is an equivalence of two membershipwise identities: that for every $v\in\mathbb{C}^2$ one has $v = \ell w + \mathrm{per}_\tau(yt)$ for some $w\in\mathrm{per}_\tau(J')$ and $y\in\Lambda$ if and only if $v = \mathrm{per}_\tau(yt)$ for some $y\in J'$; and that for every quaternion $x$ one has $x = \ell j + mt$ for some $j\in J'$, $m\in\Lambda$ if and only if $x = jt$ for some $j\in J'$. In short, $\ell\,\mathrm{per}_\tau(J') + \mathrm{per}_\tau(\Lambda t) = \mathrm{per}_\tau(J't)$ holds in $\mathbb{C}^2$ if and only if $\ell J' + \Lambda t = J't$ holds in the quaternion algebra.
--
--   This is the transfer lemma that converts a level identity stated for complex period lattices attached to a point $\tau$ of the upper half plane into the corresponding identity between $\mathbb{Z}$-submodules of the quaternion algebra itself. It is used in the Atkin–Lehner/Hecke bookkeeping for quaternionic Shimura curves, by [`QuaternionAlgebra.IsEichlerOrder.exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_units_atkinLehner_qmPeriodLattice_levelModule_iff_exists_mem_levelHeckeUSet) and by [`CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_complex_of_squarefree_of_dvd`](thm.html#CerednikDrinfeld.QM.IsCoarseModuliT.isIntegral_of_complex_of_squarefree_of_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity.lean

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

theorem QuaternionAlgebra.forall_qmPeriodLattice_levelIdentity_iff_forall_levelIdentity
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (Λ J' : Submodule ℤ ℍ[ℚ, a, b]) (t : ℍ[ℚ, a, b]) (ℓ : ℕ) (τ : UpperHalfPlane) :
    (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ y ∈ Λ, (ℓ : ℂ) • w + qmPeriodMap ι τ (y * t) = v) ↔
        ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) ↔
      (∀ x : ℍ[ℚ, a, b], (∃ j ∈ J', ∃ m ∈ Λ, (ℓ : ℤ) • j + m * t = x) ↔ ∃ j ∈ J', j * t = x) := by sorry
