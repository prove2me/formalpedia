-- Prove2me | Theorems.Thm_SoficGroups_finiteUnitarySubgroupAverage_fixed
-- name    : SoficGroups.finiteUnitarySubgroupAverage_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:22.66702+00:00
-- url     : https://prove2.me/theorems/91f2fa65-8e1b-4398-b0cc-312fac972ae7
-- title:
--   SoficGroups.finiteUnitarySubgroupAverage_fixed
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

theorem SoficGroups.finiteUnitarySubgroupAverage_fixed
    (π : UnitaryRepresentation G H)
    (K : Subgroup G) [Fintype K] (x : H) (g : K) :
    π (g : G) (finiteUnitarySubgroupAverage π K x) =
      finiteUnitarySubgroupAverage π K x := by sorry
