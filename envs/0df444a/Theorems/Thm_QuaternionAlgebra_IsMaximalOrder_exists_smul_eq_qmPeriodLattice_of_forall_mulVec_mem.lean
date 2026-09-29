-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/0decfd29-73af-587e-8106-c73148b5eb79
-- title:
--   Lattices with quaternionic multiplication are homothetic to period lattices
-- statement:
--   Let $q,q'$ be primes and $a,b\in\mathbb{Q}$, and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. that $0<a$ or $0<b$, and that for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the completed algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ has every nonzero element a unit precisely when $v$ contains the image of $q$ or of $q'$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, meaning: $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is all of $B$, it is finitely generated, and any order containing $\Lambda$ equals $\Lambda$. Let $\iota\colon B\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra homomorphism, and let $L\subseteq\mathbb{C}^2$ be a $\mathbb{Z}$-submodule which is the $\mathbb{Z}$-span of the range of some $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by $\mathrm{Fin}\,4$, and which is stable under the matrices $\iota(x)$, $x\in\Lambda$, acting on $\mathbb{C}^2$ through the entrywise map $M_2(\mathbb{R})\to M_2(\mathbb{C})$. Then there exist $\tau$ in the upper half-plane and $c\in\mathbb{C}$, $c\neq 0$, with $c\cdot L$ equal to `qmPeriodLattice ι Λ τ`, the image of $\Lambda$ under the $\mathbb{Z}$-linear map $x\mapsto \iota(x)\binom{\tau}{1}$.
--
--   This is the classification, at level one, of full lattices in $\mathbb{C}^2$ admitting multiplication by a maximal order in an indefinite rational quaternion algebra: every such lattice is homothetic to a period lattice $\iota(\Lambda)\binom{\tau}{1}$. It is used in the analytic description of the fake elliptic curves parametrised by the associated Shimura curve, and in the corresponding statement for Eichler orders (lattice pairs).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (L : Submodule ℤ (Fin 2 → ℂ))
    (hfull : ∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), L = Submodule.span ℤ (Set.range e))
    (hstab : ∀ x ∈ Λ, ∀ v ∈ L, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ L) :
    ∃ (τ : UpperHalfPlane) (c : ℂ), c ≠ 0 ∧ c • L = qmPeriodLattice ι Λ τ := by sorry
