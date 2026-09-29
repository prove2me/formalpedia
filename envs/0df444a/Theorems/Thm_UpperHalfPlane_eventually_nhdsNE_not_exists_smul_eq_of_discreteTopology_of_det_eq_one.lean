-- Prove2me | Theorems.Thm_UpperHalfPlane_eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one
-- name    : UpperHalfPlane.eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/eebbe556-b0cb-5ec3-a1ce-dc8be4543114
-- title:
--   Orbits of a discrete determinant-one subgroup of GL₂(ℝ) are discrete
-- statement:
--   Let $\Gamma$ be a subgroup of $GL_2(\mathbb{R})$ whose underlying subtype carries the discrete topology (for the topology induced from $GL_2(\mathbb{R})$), and assume that every $\gamma \in \Gamma$ has determinant $1$, the determinant being taken as the unit `Matrix.GeneralLinearGroup.det` of $\mathbb{R}$. Let $\tau, \tau'$ be points of the upper half plane $\mathfrak{H}$. The conclusion is an assertion about the punctured neighbourhood filter $\mathcal{N}_{\neq}(\tau) = \mathfrak{N}[\neq]\,\tau$: eventually, for $z$ in that filter, there is no $\gamma \in \Gamma$ with $\gamma \cdot \tau' = z$, the action being the action of $GL_2(\mathbb{R})$ on $\mathfrak{H}$, which restricts along $SL_2(\mathbb{R}) \to GL_2(\mathbb{R})$ to the usual Möbius action. Equivalently, some open neighbourhood $U$ of $\tau$ satisfies $(U \setminus \{\tau\}) \cap \Gamma\tau' = \emptyset$: the orbit $\Gamma\tau'$ does not accumulate at $\tau$. Note that $\tau$ itself is allowed to lie in the orbit; the statement is the local one at each single point $\tau$, from which closedness and discreteness of the orbit follow.
--
--   This is the standard fact that a discrete subgroup of $SL_2(\mathbb{R})$ (a Fuchsian group) acts properly discontinuously on the upper half plane, so that each of its orbits is a closed discrete subset, stated here in the local 'no accumulation at $\tau$' form. It is used in the Čerednik–Drinfeld part of the development, to show that a locus defined by the existence of a group element carrying one lattice to another is closed, and in the construction of period maps for meromorphic realizations on uniformized Hecke curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups Topology

theorem UpperHalfPlane.eventually_nhdsNE_not_exists_smul_eq_of_discreteTopology_of_det_eq_one
    (Γ : Subgroup (GL (Fin 2) ℝ)) [DiscreteTopology ↥Γ]
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (τ τ' : UpperHalfPlane) :
    ∀ᶠ z in 𝓝[≠] τ, ¬ ∃ γ ∈ Γ, γ • τ' = z := by sorry
