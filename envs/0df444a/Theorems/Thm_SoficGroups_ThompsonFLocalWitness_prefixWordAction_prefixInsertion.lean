-- Prove2me | Theorems.Thm_SoficGroups_ThompsonFLocalWitness_prefixWordAction_prefixInsertion
-- name    : SoficGroups.ThompsonFLocalWitness.prefixWordAction_prefixInsertion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/2d8643f8-0bd8-45df-b8bc-fb595cb3998e
-- title:
--   SoficGroups.ThompsonFLocalWitness.prefixWordAction_prefixInsertion
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion

theorem SoficGroups.ThompsonFLocalWitness.prefixWordAction_prefixInsertion {g : BinaryLeavittˣ}
    {a b : List (Fin 2)} (l : List (Fin 2))
    (h : PrefixWordAction g a b) :
    PrefixWordAction (prefixInsertionHom l g) (l ++ a) (l ++ b) := by sorry
