-- Prove2me | Theorems.Thm_SoficGroups_unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
-- name    : SoficGroups.unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/d33dfbd9-5dfb-46b7-a950-3f8cbee6556d
-- title:
--   SoficGroups.unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁

theorem SoficGroups.unitaryFixedSubmodule_starProjection_mem_orthogonal_of_commute
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : UnitaryRepresentation G H) (K Z : Subgroup G)
    (hcomm : ∀ k : K, ∀ z : Z, Commute (k : G) (z : G))
    {x : H} (hx : x ∈ (unitaryFixedSubmodule π Z)ᗮ) :
    (unitaryFixedSubmodule π K).starProjection x ∈
      (unitaryFixedSubmodule π Z)ᗮ := by sorry
