-- Prove2me | Theorems.Thm_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one
-- name    : UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/f4502d0b-1fa5-5aef-89d7-b2577c9554ff
-- title:
--   Point stabilisers in discrete determinant-one subgroups are finite cyclic
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ such that every $\gamma \in \Gamma$ has determinant $1$ (as an element of $\mathbb{R}^\times$, i.e. `Matrix.GeneralLinearGroup.det γ = 1`), and suppose that $\Gamma$, with the topology induced from $\mathrm{GL}_2(\mathbb{R})$, is discrete. Let $\tau$ be a point of the upper half plane $\mathbb{H}$. Then the stabiliser of $\tau$ for the action of $\Gamma$ on $\mathbb{H}$ by Möbius transformations, i.e. the subgroup $\{\gamma \in \Gamma : \gamma \cdot \tau = \tau\}$, is both finite and cyclic: the assertion is the conjunction of `Finite` and `IsCyclic` for that stabiliser subgroup. No further hypothesis on $\Gamma$ (such as being contained in the image of $\mathrm{SL}_2(\mathbb{Z})$, or acting with quotient of finite volume) is imposed, and the conclusion is stated for a single arbitrary point $\tau$.
--
--   This is the classical statement that a point of the upper half plane has finite cyclic stabiliser in a discrete subgroup of $\mathrm{SL}_2(\mathbb{R})$, which is the local structure underlying the orbifold charts on modular curves. It is used in the construction of local parameters and of modular forms with prescribed behaviour at a point, for instance by [`ModularCurve.exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology`](thm.html#ModularCurve.exists_modularForm_ne_zero_le_meromorphicOrderAt_of_discreteTopology), [`ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology`](thm.html#ModularCurve.exists_modularForm_separate_and_localParameter_of_discreteTopology) and [`ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete`](thm.html#ModularCurve.UniformizedHeckeCurve.exists_of_isCompact_of_discrete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_UpperHalfPlane_finite_stabilizer_and_isCyclic_of_det_eq_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter UpperHalfPlane
open scoped MatrixGroups Topology

theorem UpperHalfPlane.finite_stabilizer_and_isCyclic_of_det_eq_one
    (Γ : Subgroup (GL (Fin 2) ℝ))
    (hdet : ∀ γ ∈ Γ, Matrix.GeneralLinearGroup.det γ = 1)
    [hdisc : DiscreteTopology ↥Γ] (τ : ℍ) :
    Finite ↥(MulAction.stabilizer ↥Γ τ) ∧ IsCyclic ↥(MulAction.stabilizer ↥Γ τ) := by sorry
