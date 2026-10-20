-- Prove2me | Theorems.Thm_SoficGroups_unitaryFixedSubmodule_map_of_centralizes
-- name    : SoficGroups.unitaryFixedSubmodule_map_of_centralizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/321567d9-fd2c-4268-8ba2-ef82b9c46c01
-- title:
--   SoficGroups.unitaryFixedSubmodule_map_of_centralizes
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁

theorem SoficGroups.unitaryFixedSubmodule_map_of_centralizes
    {G : Type u₁} {H : Type v₁} [Group G]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (π : UnitaryRepresentation G H) (K : Subgroup G) (g : G)
    (hg : ∀ k : K, Commute g (k : G)) :
    (unitaryFixedSubmodule π K).map (π g).toLinearEquiv.toLinearMap =
      unitaryFixedSubmodule π K := by sorry
