-- Prove2me | Theorems.Thm_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
-- name    : QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/6c3aafb1-fcef-5f50-bdfd-2e7a681786d8
-- title:
--   Period lattice of an order is a full lattice in ℂ²
-- statement:
--   Let $a,b$ be nonzero rationals and let $\Lambda$ be a $\mathbb{Z}$-submodule of the rational quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the project predicate `IsOrder`: $1 \in \Lambda$, $\Lambda$ is closed under multiplication, its $\mathbb{Q}$-span is all of $\mathbb{H}[\mathbb{Q},a,b]$, and it is finitely generated over $\mathbb{Z}$. Let $\iota \colon \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$ be a homomorphism of $\mathbb{Q}$-algebras and let $\tau$ be a point of the upper half-plane. Write $\pi_\tau$ for the $\mathbb{Z}$-linear map `qmPeriodMap` sending $x$ to the vector $\iota(x)\,(\tau,1)^{t} \in \mathbb{C}^2$, obtained by entrywise inclusion $\mathbb{R} \hookrightarrow \mathbb{C}$ of the matrix $\iota(x)$ followed by multiplication with the column vector $(\tau,1)$, and let $\Lambda_\tau := \pi_\tau(\Lambda)$ be the image submodule `qmPeriodLattice`. The conclusion is fourfold: $\pi_\tau$ is injective on the whole of $\mathbb{H}[\mathbb{Q},a,b]$; there is a basis $e$ of $\mathbb{C}^2$ as a four-dimensional real vector space, indexed by `Fin 4`, with $\Lambda_\tau$ equal to the $\mathbb{Z}$-span of the range of $e$; $\Lambda_\tau$, with its subspace topology, is discrete; and the $\mathbb{R}$-span of $\Lambda_\tau$ inside $\mathbb{C}^2$ is everything.
--
--   This is the linear-algebra input to the uniformisation of abelian surfaces with quaternionic multiplication: it says that $\mathbb{C}^2/\Lambda_\tau$ is a two-dimensional complex torus carrying an action of $\Lambda$ through $\iota$. It is used in the construction of the period charts and of the fine moduli description of fake elliptic curves in the Čerednik–Drinfel'd part of the development, and in the comparison of period lattices attached to pairs of Eichler orders.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_IsOrder_qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span.lean

import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise
open QuaternionAlgebra

theorem QuaternionAlgebra.IsOrder.qmPeriodMap_injective_and_exists_basis_qmPeriodLattice_eq_span
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (τ : UpperHalfPlane) :
    Function.Injective (qmPeriodMap ι τ) ∧
      (∃ e : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ), qmPeriodLattice ι Λ τ = Submodule.span ℤ (Set.range e)) ∧
      DiscreteTopology (qmPeriodLattice ι Λ τ) ∧
      Submodule.span ℝ (qmPeriodLattice ι Λ τ : Set (Fin 2 → ℂ)) = ⊤ := by sorry
