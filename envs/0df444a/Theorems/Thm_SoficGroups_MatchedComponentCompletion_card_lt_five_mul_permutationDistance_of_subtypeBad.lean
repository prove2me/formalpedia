-- Prove2me | Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_lt_five_mul_permutationDistance_of_subtypeBad
-- name    : SoficGroups.MatchedComponentCompletion.card_lt_five_mul_permutationDistance_of_subtypeBad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/3fba4cf5-b779-4f99-84bf-bbbd66a7f668
-- title:
--   SoficGroups.MatchedComponentCompletion.card_lt_five_mul_permutationDistance_of_subtypeBad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators

theorem SoficGroups.MatchedComponentCompletion.card_lt_five_mul_permutationDistance_of_subtypeBad
    {V : Type*} [DecidableEq V]
    (Z E : Finset V) (hZ : Z.Nonempty)
    (p q : Equiv.Perm {x : V // x ∈ Z})
    (hbad : 5 * (subtypeBad Z E).card ≤ Fintype.card {x : V // x ∈ Z})
    (hseparated : ∀ x : {x : V // x ∈ Z},
      (x : V) ∉ E → p x ≠ q x) :
    Fintype.card {x : V // x ∈ Z} <
      5 * SoficGroups.permutationDistance p q := by sorry
