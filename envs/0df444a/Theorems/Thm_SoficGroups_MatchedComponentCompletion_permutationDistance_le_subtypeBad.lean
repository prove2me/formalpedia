-- Prove2me | Theorems.Thm_SoficGroups_MatchedComponentCompletion_permutationDistance_le_subtypeBad
-- name    : SoficGroups.MatchedComponentCompletion.permutationDistance_le_subtypeBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/43858955-9b19-4d54-995a-2fa1e3e93754
-- title:
--   SoficGroups.MatchedComponentCompletion.permutationDistance_le_subtypeBad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators

theorem SoficGroups.MatchedComponentCompletion.permutationDistance_le_subtypeBad
    {V : Type*} [DecidableEq V]
    (Z E : Finset V)
    (p q : Equiv.Perm {x : V // x ∈ Z})
    (hagrees : ∀ x : {x : V // x ∈ Z},
      (x : V) ∉ E → p x = q x) :
    SoficGroups.permutationDistance p q ≤ (subtypeBad Z E).card := by sorry
