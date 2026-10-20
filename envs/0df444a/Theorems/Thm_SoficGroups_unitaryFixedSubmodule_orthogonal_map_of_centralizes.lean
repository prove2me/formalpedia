-- Prove2me | Theorems.Thm_SoficGroups_unitaryFixedSubmodule_orthogonal_map_of_centralizes
-- name    : SoficGroups.unitaryFixedSubmodule_orthogonal_map_of_centralizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/d91209c3-2372-4a71-a5e8-b97e7d715af5
-- title:
--   SoficGroups.unitaryFixedSubmodule_orthogonal_map_of_centralizes
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁

theorem SoficGroups.unitaryFixedSubmodule_orthogonal_map_of_centralizes
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (Z : Subgroup G) (g : G)
    (hg : ∀ z : Z, Commute g (z : G))
    {x : H} (hx : x ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    π g x ∈ (unitaryFixedSubmodule π Z)ᗮ := by sorry
