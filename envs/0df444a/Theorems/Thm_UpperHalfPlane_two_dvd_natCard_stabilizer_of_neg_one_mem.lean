-- Prove2me | Theorems.Thm_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem
-- name    : UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/75553465-180b-5920-ae87-9b1f5471746f
-- title:
--   Even order of stabilisers when -1 ∈ Γ
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ all of whose elements have determinant $1$, carrying the discrete topology as a subspace of $\mathrm{GL}_2(\mathbb{R})$, and assume that the matrix $-1$ belongs to $\Gamma$. Let $\tau$ be a point of the upper half plane $\mathbb{H}$, on which $\Gamma$ acts through the usual action of $\mathrm{GL}_2(\mathbb{R})$ on $\mathbb{H}$ by fractional linear transformations. Then $2$ divides the cardinality, as a natural number, of the stabiliser subgroup $\mathrm{Stab}_\Gamma(\tau) = \{\gamma \in \Gamma : \gamma \cdot \tau = \tau\}$. (The cardinality is taken in the sense of `Nat.card`, so the assertion would be vacuous for an infinite stabiliser; finiteness of the stabiliser is in fact part of what the proof establishes, via the companion result for discrete determinant-one subgroups.)
--
--   This is the standard observation that for a discrete subgroup of $\mathrm{SL}_2(\mathbb{R})$ containing $-1$ the stabiliser of a point of $\mathbb{H}$ has even order, so that the ramification index $e_\tau = \#\mathrm{Stab}_\Gamma(\tau)/2$ of the quotient map $\mathbb{H} \to \Gamma\backslash\mathbb{H}$ at $\tau$ is a positive integer. It is used in the construction of uniformized Hecke curves and in the existence statements for modular forms with prescribed order or separating behaviour on such quotients.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_two_dvd_natCard_stabilizer_of_neg_one_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.two_dvd_natCard_stabilizer_of_neg_one_mem
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    (hneg : -1 ∈ Γ)
    [hdisc : DiscreteTopology ↥Γ] (τ : ℍ) :
    2 ∣ Nat.card ↥(MulAction.stabilizer ↥Γ τ) := by sorry
