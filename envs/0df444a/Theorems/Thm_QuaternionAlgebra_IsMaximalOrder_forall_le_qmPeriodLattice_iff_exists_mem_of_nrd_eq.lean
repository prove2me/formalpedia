-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq
-- name    : QuaternionAlgebra.IsMaximalOrder.forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/f502b5b4-3a4b-5f7d-b472-b9201085c00a
-- title:
--   Hecke dictionary for quaternionic period lattices
-- statement:
--   Let $q \neq q'$ be primes, let $a,b \in \mathbb{Q}$ be such that the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`, i.e. $0 < a$ or $0 < b$, and for every height-one prime $v$ of the ring of integers of $\mathbb{Q}$ every nonzero element of the base change to the $v$-adic completion is a unit precisely when $v$ contains $q$ or $q'$. Let $\Lambda$ be a $\mathbb{Z}$-submodule which is a maximal order (it contains $1$, is closed under multiplication, is finitely generated, spans the algebra over $\mathbb{Q}$, and any order containing it equals it), let $\iota$ be an injective $\mathbb{Q}$-algebra map into $M_2(\mathbb{R})$, let $\tau$ lie in the upper half-plane, let $\ell$ be prime, and let $S$ be a finite set of elements of $\Lambda$ of reduced norm $\ell$ such that every $y \in \Lambda$ with $\mathrm{nrd}\, y = \ell$ is $u x$ for a unique $x \in S$ and some two-sided unit $u$ of $\Lambda$ of reduced norm $1$. Write $L_\tau = \mathrm{qmPeriodLattice}\,\iota\,\Lambda\,\tau$ for the image of $\Lambda$ under $x \mapsto \iota(x)\binom{\tau}{1}$ in $\mathbb{C}^2$. Three assertions are made. First, a $\mathbb{Z}$-submodule $M \subseteq \mathbb{C}^2$ satisfies $M \le L_\tau$, $\ell L_\tau \subseteq M$, stability under the matrices $\iota(y)$ for $y \in \Lambda$ (complexified, acting by `mulVec`), and relative index $\ell^2$ in $L_\tau$, if and only if $M = \{\iota(ys)\binom{\tau}{1} : y \in \Lambda\}$ for some $s \in S$. Secondly, distinct elements of $S$ give distinct such submodules. Thirdly, for each $s \in S$ there is $g \in \mathrm{GL}_2(\mathbb{R})$ with underlying matrix $\iota(s)$ and positive determinant such that $\{\iota(ys)\binom{\tau}{1} : y \in \Lambda\}$ equals $\mathrm{denom}(g,\tau) \cdot L_{g\tau}$.
--
--   This is the lattice form of the Hecke correspondence at $\ell$ for quaternionic multiplication: the $\Lambda$-stable sublattices of index $\ell^2$ between $\ell L_\tau$ and $L_\tau$ are parametrised bijectively by the norm-$\ell$ representatives in $S$, each being homothetic to the period lattice of the translated point $\iota(s)\tau$. It supplies the lattice-theoretic input for the identification of isogeny quotients of the fake elliptic curves attached to points of the Shimura curve with their Hecke translates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsMaximalOrder_forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsMaximalOrder.forall_le_qmPeriodLattice_iff_exists_mem_of_nrd_eq
    {q q' : ℕ} [Fact q.Prime] [Fact q'.Prime] (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (S : Finset ℍ[ℚ, a, b]) (hS : ∀ x ∈ S, x ∈ Λ ∧ nrd x = (ℓ : ℚ))
    (hSrep : ∀ y : ℍ[ℚ, a, b], y ∈ Λ → nrd y = (ℓ : ℚ) →
      ∃! x, x ∈ S ∧ ∃ u : ℍ[ℚ, a, b], IsUnitOf Λ u ∧ nrd u = 1 ∧ u * x = y) :

    (∀ M : Submodule ℤ (Fin 2 → ℂ),
      (M ≤ qmPeriodLattice ι Λ τ ∧
        (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M) ∧
        (∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M) ∧
        M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2) ↔
      ∃ s ∈ S, ∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ∧

    (∀ s ∈ S, ∀ s' ∈ S,
      (∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ↔ (∃ y ∈ Λ, qmPeriodMap ι τ (y * s') = v)) → s = s') ∧

    (∀ s ∈ S, ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = ι s ∧ 0 < g.det.val ∧
      ∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * s) = v) ↔
        v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ)) := by sorry
