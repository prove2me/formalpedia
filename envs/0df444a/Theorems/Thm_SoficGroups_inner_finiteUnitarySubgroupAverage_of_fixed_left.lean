-- Prove2me | Theorems.Thm_SoficGroups_inner_finiteUnitarySubgroupAverage_of_fixed_left
-- name    : SoficGroups.inner_finiteUnitarySubgroupAverage_of_fixed_left
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/10531fe4-2037-4956-bc35-0f9aca4ef125
-- title:
--   SoficGroups.inner_finiteUnitarySubgroupAverage_of_fixed_left
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u₁ v₁
variable {G : Type*} {H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem SoficGroups.inner_finiteUnitarySubgroupAverage_of_fixed_left
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (a b : H)
    (ha : ∀ k : K, π (k : G) a = a) :
    inner ℂ a (finiteUnitarySubgroupAverage π K b) =
      inner ℂ a b := by sorry
