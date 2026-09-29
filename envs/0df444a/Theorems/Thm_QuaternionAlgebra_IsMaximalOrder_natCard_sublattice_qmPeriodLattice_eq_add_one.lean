-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_natCard_sublattice_qmPeriodLattice_eq_add_one
-- name    : QuaternionAlgebra.IsMaximalOrder.natCard_sublattice_qmPeriodLattice_eq_add_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/d1665370-a645-525f-bab9-d1cebec7ca9f
-- title:
--   Counting Λ-stable sublattices of index ℓ² in a period lattice
-- statement:
--   Let $q,q'$ be primes with $q'\neq q$, let $a,b\in\mathbb{Q}$, and let $B=\mathbb{H}[\mathbb{Q},a,b]$ be the quaternion algebra over $\mathbb{Q}$ with parameters $a,b$. Assume `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0<a$ or $0<b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ the algebra $B\otimes_{\mathbb{Q}}\mathbb{Q}_v$ is a division algebra (every nonzero element is a unit) exactly when $q\in v$ or $q'\in v$. Let $\Lambda\subseteq B$ be a $\mathbb{Z}$-submodule which is a maximal order: it contains $1$, is closed under multiplication, spans $B$ over $\mathbb{Q}$, is finitely generated, and every order containing it equals it. Let $\iota\colon B\to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra map, $\tau$ a point of the upper half-plane, and write $L=$ `qmPeriodLattice ι Λ τ` for the image of $\Lambda$ under $x\mapsto \iota(x)\cdot{}^{t}(\tau,1)$, the matrix being read in $M_2(\mathbb{C})$. Let $\ell$ be a prime with $\ell\neq q$ and $\ell\neq q'$. Then the number of $\mathbb{Z}$-submodules $M\subseteq\mathbb{C}^2$ with $M\le L$, $\ell L\subseteq M$, $\iota(y)M\subseteq M$ for all $y\in\Lambda$, and relative index of $M$ in $L$ equal to $\ell^2$, is $\ell+1$.
--
--   This is the lattice-theoretic count of the $\ell+1$ level-$\ell$ structures, or $\ell$-isogenies, on a fake elliptic curve attached to a maximal order in an indefinite quaternion algebra ramified exactly at $q,q'$: via the period map the admissible $M$ correspond to the proper lines in $\Lambda/\ell\Lambda\cong M_2(\mathbb{F}_\ell)$. It is used in the construction of extra level structure on points of the associated Shimura curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_natCard_sublattice_qmPeriodLattice_eq_add_one.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.natCard_sublattice_qmPeriodLattice_eq_add_one
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :
    Nat.card {M : Submodule ℤ (Fin 2 → ℂ) //
        M ≤ qmPeriodLattice ι Λ τ ∧
        (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M) ∧
        (∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M) ∧
        M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2} = ℓ + 1 := by sorry
