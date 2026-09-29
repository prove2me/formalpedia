-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
-- name    : QuaternionAlgebra.IsEichlerOrder.forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.214879+00:00
-- url     : https://prove2.me/theorems/bdd1fec5-89b6-581b-93e3-057ca71e4e8f
-- title:
--   Norm-ℓ elements of an Eichler order and period sublattices
-- statement:
--   Fix natural numbers $N,q,q'$ with $N\neq 0$, $q$ and $q'$ prime, $q\nmid N$, $q'\nmid N$ and $q'\neq q$, and rationals $a,b$ such that $\mathbb H[\mathbb Q,a,b]$ satisfies `IsIndefiniteRamifiedExactlyAt a b q q'`: $0<a$ or $0<b$, and for every height-one prime $v$ of the integers of $\mathbb Q$ the completed algebra $\mathbb H[\mathbb Q,a,b]\otimes_{\mathbb Q}\mathbb Q_v$ has all nonzero elements invertible exactly when $q\in v$ or $q'\in v$. Let $\Lambda$ be a maximal order (an order in the sense of containing $1$, closed under multiplication, $\mathbb Q$-spanning and finitely generated, and maximal among such), $N$ squarefree, $R\subseteq\Lambda$ an Eichler order of level $N$ (an intersection $\Lambda_1\cap\Lambda_2$ of maximal orders with $[\Lambda_1:R]=N$), and $\iota:\mathbb H[\mathbb Q,a,b]\to M_2(\mathbb R)$ an injective $\mathbb Q$-algebra map. Let $J'\supseteq\Lambda$ be a $\mathbb Z$-submodule with $\Lambda J'\subseteq J'$, $NJ'\subseteq\Lambda$, $[J':\Lambda]=N^2$, and, for $x\in\Lambda$, $x\in R$ iff $J'x\subseteq J'$. Let $\tau$ lie in the upper half-plane and $\ell$ be a prime with $\ell\neq q,q'$. Write $L_\tau(X)$ for `qmPeriodLattice`, the image of $X$ under $x\mapsto(\iota x\otimes\mathbb C)\binom{\tau}{1}$. Three assertions are made. First, a $\mathbb Z$-submodule $M\subseteq\mathbb C^2$ satisfies $M\subseteq L_\tau(\Lambda)$, $\ell L_\tau(\Lambda)\subseteq M$, stability of $M$ under the complexified matrices $\iota(y)$ for $y\in\Lambda$, $[L_\tau(\Lambda):M]=\ell^2$, and the transversality $v\in L_\tau(J')$, $\ell v\in M\Rightarrow v\in L_\tau(\Lambda)$, if and only if there is $t\in R$ with $\mathrm{nrd}\,t=\ell$ such that $M$ is the set of periods of $\Lambda t$ and $\ell L_\tau(J')+M$ is the set of periods of $J't$. Second, if $t,t'\in R$ have reduced norm $\ell$, if $\ell L_\tau(J')+L_\tau(\Lambda t)$ equals the period set of $J't$, and if $\Lambda t$ and $\Lambda t'$ have the same period set, then $t'=ut$ for some $u\in R$ with a two-sided inverse in $R$ and $\mathrm{nrd}\,u=1$. Third, for every $t\in R$ with $\mathrm{nrd}\,t=\ell$ there is $g\in GL_2(\mathbb R)$ whose matrix is $\iota t$, with positive determinant, such that the period set of $\Lambda t$ is $\mathrm{denom}(g,\tau)\cdot L_{g\tau}(\Lambda)$ and that of $J't$ is $\mathrm{denom}(g,\tau)\cdot L_{g\tau}(J')$.
--
--   This is the lattice dictionary for the Hecke correspondence $T_\ell$ on quaternionic (Shimura) curves with Eichler level structure: admissible index-$\ell^2$ sublattices of the period lattice of a maximal order, transversal to the level lattice $J'$, correspond to norm-$\ell$ elements of the Eichler order modulo left multiplication by norm-one units, and are realised analytically at the translated point $\iota(t)\tau$. It is used in the construction of the Hecke correspondences on uniformised quaternionic curves and in the integrality and level-structure statements for families of fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsEichlerOrder_forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra CerednikDrinfeld

theorem QuaternionAlgebra.IsEichlerOrder.forall_le_qmPeriodLattice_transversal_iff_exists_mem_nrd_eq
    {N q q' : ℕ} [NeZero N] [Fact q.Prime] [Fact q'.Prime] (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N) (hqq' : q' ≠ q)
    {a b : ℚ} (hB : IsIndefiniteRamifiedExactlyAt a b q q')
    (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ)
    (hN : Squarefree N) (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b])
    (hJ' : Λ ≤ J' ∧ (∀ x ∈ Λ, ∀ y ∈ J', x * y ∈ J') ∧ (∀ y ∈ J', ((N : ℤ) • y) ∈ Λ) ∧
      Λ.toAddSubgroup.relIndex J'.toAddSubgroup = N ^ 2 ∧ (∀ x ∈ Λ, x ∈ R ↔ ∀ y ∈ J', y * x ∈ J'))
    (τ : UpperHalfPlane) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓq' : ℓ ≠ q') :

    (∀ M : Submodule ℤ (Fin 2 → ℂ),
      (M ≤ qmPeriodLattice ι Λ τ ∧
        (∀ v ∈ qmPeriodLattice ι Λ τ, (ℓ : ℤ) • v ∈ M) ∧
        (∀ y ∈ Λ, ∀ v ∈ M, ((ι y).map (algebraMap ℝ ℂ)).mulVec v ∈ M) ∧
        M.toAddSubgroup.relIndex (qmPeriodLattice ι Λ τ).toAddSubgroup = ℓ ^ 2 ∧
        (∀ v ∈ qmPeriodLattice ι J' τ, (ℓ : ℂ) • v ∈ M → v ∈ qmPeriodLattice ι Λ τ)) ↔
      ∃ t ∈ R, nrd t = (ℓ : ℚ) ∧
        (∀ v : Fin 2 → ℂ, v ∈ M ↔ ∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ∧
        (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ m ∈ M, (ℓ : ℂ) • w + m = v) ↔
          ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v)) ∧

    (∀ t t' : ℍ[ℚ, a, b], t ∈ R → t' ∈ R → nrd t = (ℓ : ℚ) → nrd t' = (ℓ : ℚ) →
      (∀ v : Fin 2 → ℂ, (∃ w ∈ qmPeriodLattice ι J' τ, ∃ y ∈ Λ, (ℓ : ℂ) • w + qmPeriodMap ι τ (y * t) = v) ↔
        ∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) →
      (∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ↔ (∃ y ∈ Λ, qmPeriodMap ι τ (y * t') = v)) →
      ∃ u : ℍ[ℚ, a, b], IsUnitOf R u ∧ nrd u = 1 ∧ u * t = t') ∧

    (∀ t : ℍ[ℚ, a, b], t ∈ R → nrd t = (ℓ : ℚ) →
      ∃ g : GL (Fin 2) ℝ, (g : Matrix (Fin 2) (Fin 2) ℝ) = ι t ∧ 0 < g.det.val ∧
        (∀ v : Fin 2 → ℂ, (∃ y ∈ Λ, qmPeriodMap ι τ (y * t) = v) ↔
          v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι Λ (g • τ)) ∧
        (∀ v : Fin 2 → ℂ, (∃ y ∈ J', qmPeriodMap ι τ (y * t) = v) ↔
          v ∈ UpperHalfPlane.denom g τ • qmPeriodLattice ι J' (g • τ))) := by sorry
