-- Prove2me | Theorems.Thm_QuaternionAlgebra_smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap
-- name    : QuaternionAlgebra.smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.566428+00:00
-- url     : https://prove2.me/theorems/a08a7813-9e9c-5579-92b2-89332730a1d8
-- title:
--   Propagating a period-lattice identity across a parameter set
-- statement:
--   Fix rationals $a,b$ and let $\iota : \mathbb{H}[\mathbb{Q},a,b] \to M_2(\mathbb{R})$ be an injective $\mathbb{Q}$-algebra homomorphism, where for $\tau$ in the upper half-plane `qmPeriodMap ι τ` denotes the $\mathbb{Z}$-linear map $x \mapsto (\iota x)\,(\tau,1)^{t}$, entries regarded in $\mathbb{C}$, and `qmPeriodLattice ι Λ τ` its image on a $\mathbb{Z}$-submodule $\Lambda$. Let $J'$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$, $N$ a nonzero natural number, $D \subseteq \mathbb{C}$ a set with a point $z_0 \in D$, and let there be given families $L, ME$ of $\mathbb{Z}$-submodules of $\mathbb{C}^2$, scalar functions $\kappa, c : \mathbb{C} \to \mathbb{C}$, vectors $v_i : \mathbb{C} \to \mathbb{C}^2$ for $i \in \{0,1,2,3\}$, elements $y_i \in \mathbb{H}[\mathbb{Q},a,b]$, a map $\tau : \mathbb{C} \to \mathfrak{h}$ and a set $T \subseteq \mathbb{Z}^4$. Assume for each $z \in D$: $\kappa z \neq 0$ and $c z \neq 0$; the $v_i(z)$ lie in the pointwise dilate $\kappa z \cdot L z$ and every element of $\kappa z \cdot L z$ is $\sum_i n_i v_i(z)$ for a unique $n \in \mathbb{Z}^4$; $w \in ME z$ if and only if $w \equiv \kappa(z)^{-1} N^{-1} \sum_i n_i v_i(z)$ modulo $L z$ for some $n \in T$; and $c z \cdot v_i(z) =$ `qmPeriodMap ι (τ z) (y i)` for all $i$. Assume finally $(c z_0 \kappa z_0) \cdot ME z_0 =$ `qmPeriodLattice ι J' (τ z₀)`. Then $(c z \,\kappa z) \cdot ME z =$ `qmPeriodLattice ι J' (τ z)` for every $z \in D$.
--
--   A rigidity statement for quaternionic period lattices: the data $T$, $y$, $N$ and $J'$ do not depend on the parameter $z$, so one identification of the $ME$-lattice with the period lattice of $J'$ forces it at all points of $D$. It is used in the construction of period charts for fine moduli of quaternionic multiplication in the Čerednik–Drinfeld setting, both with and without full level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_QuaternionAlgebra_smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap.lean

import Definitions.Def_QuaternionAlgebra_QMPeriodLattice

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups Pointwise BigOperators
open QuaternionAlgebra

theorem QuaternionAlgebra.smul_eq_qmPeriodLattice_of_forall_mem_iff_of_smul_eq_qmPeriodMap
    {a b : ℚ} (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (J' : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) [NeZero N]
    (D : Set ℂ) (z₀ : ℂ) (hz₀ : z₀ ∈ D)
    (L ME : ℂ → Submodule ℤ (Fin 2 → ℂ)) (κ c : ℂ → ℂ) (v : Fin 4 → ℂ → (Fin 2 → ℂ))
    (y : Fin 4 → ℍ[ℚ, a, b]) (τ : ℂ → UpperHalfPlane) (T : Set (Fin 4 → ℤ))
    (hκ : ∀ z ∈ D, κ z ≠ 0) (hc : ∀ z ∈ D, c z ≠ 0)
    (hbasis : ∀ z ∈ D,
      (∀ i : Fin 4, v i z ∈ κ z • L z) ∧ ∀ x ∈ κ z • L z, ∃! n : Fin 4 → ℤ, (∑ i, (n i : ℂ) • v i z) = x)
    (hME : ∀ z ∈ D, ∀ w : Fin 2 → ℂ,
      w ∈ ME z ↔ ∃ n ∈ T, (w : (Fin 2 → ℂ) ⧸ (L z).toAddSubgroup) =
        (((κ z)⁻¹ • (((N : ℂ)⁻¹) • ∑ i, (n i : ℂ) • v i z) : Fin 2 → ℂ) : (Fin 2 → ℂ) ⧸ (L z).toAddSubgroup))
    (hper : ∀ z ∈ D, ∀ i : Fin 4, c z • v i z = qmPeriodMap ι (τ z) (y i))
    (h₀ : (c z₀ * κ z₀) • ME z₀ = qmPeriodLattice ι J' (τ z₀)) :
    ∀ z ∈ D, (c z * κ z) • ME z = qmPeriodLattice ι J' (τ z) := by sorry
