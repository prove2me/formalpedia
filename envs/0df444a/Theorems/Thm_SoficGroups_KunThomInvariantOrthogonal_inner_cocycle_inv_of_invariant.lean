-- Prove2me | Theorems.Thm_SoficGroups_KunThomInvariantOrthogonal_inner_cocycle_inv_of_invariant
-- name    : SoficGroups.KunThomInvariantOrthogonal.inner_cocycle_inv_of_invariant
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:25.142856+00:00
-- url     : https://prove2.me/theorems/e86fdb12-e5ee-4cae-9e92-47e21bb0c77c
-- title:
--   SoficGroups.KunThomInvariantOrthogonal.inner_cocycle_inv_of_invariant
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SoficGroups.KunThomInvariantOrthogonal.inner_cocycle_inv_of_invariant
    (π : SoficGroups.UnitaryRepresentation G H) (b : G → H)
    (hb : ∀ g h : G, b (g * h) = b g + π g (b h))
    (y : H) (hy : ∀ g : G, π g y = y) (g : G) :
    @inner ℂ H _ y (b g⁻¹) = -@inner ℂ H _ y (b g) := by sorry
