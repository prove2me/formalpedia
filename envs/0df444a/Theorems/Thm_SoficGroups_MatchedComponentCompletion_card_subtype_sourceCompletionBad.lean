-- Prove2me | Theorems.Thm_SoficGroups_MatchedComponentCompletion_card_subtype_sourceCompletionBad
-- name    : SoficGroups.MatchedComponentCompletion.card_subtype_sourceCompletionBad
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/8611cce8-5fa9-461c-9304-d4ef20242ea3
-- title:
--   SoficGroups.MatchedComponentCompletion.card_subtype_sourceCompletionBad
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentCompletion
open scoped BigOperators

theorem SoficGroups.MatchedComponentCompletion.card_subtype_sourceCompletionBad
    {V ι J : Type*} [DecidableEq V]
    [Fintype ι] [Group J]
    (σ : ι → Equiv.Perm V) (p : J → Equiv.Perm V)
    (F : Finset J) (Z : Finset V) :
    (subtypeBad Z (sourceCompletionBad σ p F Z)).card =
      (sourceCompletionBad σ p F Z).card := by sorry
