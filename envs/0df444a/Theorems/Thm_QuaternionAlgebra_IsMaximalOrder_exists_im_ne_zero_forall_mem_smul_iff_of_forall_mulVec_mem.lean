-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
-- name    : QuaternionAlgebra.IsMaximalOrder.exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/f573f8bb-3dba-59dc-922d-06f651cfff50
-- title:
--   Lattices with quaternionic multiplication, maximal order case
-- statement:
--   Let $q,q'$ be primes and $a,b\in\mathbb{Q}$, and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`: either $a>0$ or $b>0$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$, the algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ (the $v$-adic completion) has every nonzero element invertible precisely when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order, i.e. $1\in\Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is all of $B$, it is finitely generated over $\mathbb{Z}$, and every order containing $\Lambda$ equals $\Lambda$. Let $\iota:B\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra homomorphism, and let $L\subseteq\mathbb{C}^2$ be a $\mathbb{Z}$-submodule which is the $\mathbb{Z}$-span of the range of some $\mathbb{R}$-basis of $\mathbb{C}^2$ indexed by `Fin 4`, and which is stable under the matrices $\iota(x)$, $x\in\Lambda$, acting on $\mathbb{C}^2$ via the entrywise inclusion $M_2(\mathbb{R})\subseteq M_2(\mathbb{C})$. Then there exist $\tau\in\mathbb{C}$ with $\operatorname{Im}\tau\neq0$ and $c\in\mathbb{C}^{\times}$ such that a vector $w\in\mathbb{C}^2$ lies in the dilated lattice $c\cdot L$ if and only if $w=\iota(x)\binom{\tau}{1}$ for some $x\in\Lambda$.
--
--   This is the classification, for a maximal order in an indefinite rational quaternion algebra ramified exactly at two primes, of the full lattices in $\mathbb{C}^2$ admitting quaternionic multiplication by $\Lambda$: each is a dilation of a lattice $\iota(\Lambda)\binom{\tau}{1}$ with $\tau$ non-real, the sign of $\operatorname{Im}\tau$ being left free so that both the period lattices attached to points of the upper half-plane and their complex conjugates are covered. It is used in [`QuaternionAlgebra.IsMaximalOrder.exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem`](thm.html#QuaternionAlgebra.IsMaximalOrder.exists_smul_eq_qmPeriodLattice_of_forall_mulVec_mem) and, through it, in the construction of the Shimura curve parametrising abelian surfaces with quaternionic multiplication.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsMaximalOrder.exists_im_ne_zero_forall_mem_smul_iff_of_forall_mulVec_mem
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (L : Submodule ℤ (Fin 2 → ℂ))
    (hfull : ∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), L = Submodule.span ℤ (Set.range e))
    (hstab : ∀ x ∈ Λ, ∀ v ∈ L, ((ι x).map (algebraMap ℝ ℂ)).mulVec v ∈ L) :
    ∃ (τ : ℂ) (c : ℂ), τ.im ≠ 0 ∧ c ≠ 0 ∧
      ∀ w : Fin 2 → ℂ, w ∈ c • L ↔ ∃ x ∈ Λ, ((ι x).map (algebraMap ℝ ℂ)).mulVec ![τ, 1] = w := by sorry
