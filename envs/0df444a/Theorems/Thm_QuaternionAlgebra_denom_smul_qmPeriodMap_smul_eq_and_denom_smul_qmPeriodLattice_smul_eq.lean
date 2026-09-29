-- Prove2me | Theorems.Thm_QuaternionAlgebra_denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq
-- name    : QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/84cbf875-efb5-50a6-9c26-3d946c35b4ab
-- title:
--   Automorphy of quaternionic period lattices under ι(x)
-- statement:
--   Let $a,b\in\mathbb{Q}$, let $\iota\colon \mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ be a homomorphism of $\mathbb{Q}$-algebras, let $\Lambda$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$, let $x$ be a quaternion, and let $g\in \mathrm{GL}_2(\mathbb{R})$ be a matrix which equals $\iota(x)$ and whose determinant is positive; let $\tau$ be a point of the upper half-plane. Here $\mathtt{qmPeriodMap}\ \iota\ \tau$ is the $\mathbb{Z}$-linear map sending $y$ to the product of the matrix $\iota(y)$, viewed over $\mathbb{C}$, with the column vector $(\tau,1)$, and $\mathtt{qmPeriodLattice}\ \iota\ \Lambda\ \tau$ is the image submodule of $\Lambda$ under that map; $\mathrm{denom}\,g\,\tau$ is $g_{10}\tau+g_{11}$. Three assertions are made. First, for every quaternion $y$, $\mathrm{denom}(g,\tau)\cdot(\mathtt{qmPeriodMap}\ \iota\ (g\cdot\tau))(y)=(\mathtt{qmPeriodMap}\ \iota\ \tau)(yx)$. Second, for every $v\in\mathbb{C}^2$, $v$ lies in the pointwise scalar multiple $\mathrm{denom}(g,\tau)\cdot \mathtt{qmPeriodLattice}\ \iota\ \Lambda\ (g\cdot\tau)$ if and only if $v=(\mathtt{qmPeriodMap}\ \iota\ \tau)(yx)$ for some $y\in\Lambda$. Third, if $\Lambda$ is closed under multiplication and $x$ satisfies $\mathtt{IsUnitOf}\ \Lambda\ x$, i.e. $x\in\Lambda$ and there is $v\in\Lambda$ with $xv=vx=1$, then $\mathrm{denom}(g,\tau)\cdot \mathtt{qmPeriodLattice}\ \iota\ \Lambda\ (g\cdot\tau)=\mathtt{qmPeriodLattice}\ \iota\ \Lambda\ \tau$.
--
--   This is the automorphy (equivariance) property of the period lattices attached to a $\mathbb{Z}$-submodule of a rational quaternion algebra: translating $\tau$ by $\iota(x)$ replaces the lattice, up to the factor $\mathrm{denom}(g,\tau)$, by the lattice of the right translate $\Lambda x$, and for units of a multiplicatively closed $\Lambda$ the lattice is unchanged up to homothety, so that the assignment $\tau\mapsto \mathbb{C}^2/\Lambda_\tau$ descends along the unit orbit. It is used in the treatment of Eichler orders and of uniformised Hecke curves in the Čerednik–Drinfeld part of the development, for instance in [`QuaternionAlgebra.IsEichlerOrder.exists_smul_eq_qmPeriodLattice_pair_of_forall_mulVec_mem`](thm.html#QuaternionAlgebra.IsEichlerOrder.exists_smul_eq_qmPeriodLattice_pair_of_forall_mulVec_mem) and [`CerednikDrinfeld.QM.exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd`](thm.html#CerednikDrinfeld.QM.exists_periodMap_meromorphicRealization_of_uniformizedHeckeCurve_of_two_mul_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq.lean

import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.denom_smul_qmPeriodMap_smul_eq_and_denom_smul_qmPeriodLattice_smul_eq
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (x : ℍ[ℚ, a, b]) (g : GL (Fin 2) ℝ) (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) = ι x) (hdet : 0 < g.det.val)
    (τ : UpperHalfPlane) :
    (∀ y : ℍ[ℚ, a, b], UpperHalfPlane.denom g τ • qmPeriodMap ι (g • τ) y = qmPeriodMap ι τ (y * x)) ∧
      (∀ v : Fin 2 → ℂ, v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ) ↔
        ∃ y ∈ Λ, qmPeriodMap ι τ (y * x) = v) ∧
      ((∀ ⦃y z : ℍ[ℚ, a, b]⦄, y ∈ Λ → z ∈ Λ → y * z ∈ Λ) → IsUnitOf Λ x →
        UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ) = qmPeriodLattice ι Λ τ) := by sorry
