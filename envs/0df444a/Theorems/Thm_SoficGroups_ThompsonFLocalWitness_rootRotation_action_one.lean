-- Prove2me | Theorems.Thm_SoficGroups_ThompsonFLocalWitness_rootRotation_action_one
-- name    : SoficGroups.ThompsonFLocalWitness.rootRotation_action_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/20ae54d3-7257-4470-b111-e3cf1410e486
-- title:
--   SoficGroups.ThompsonFLocalWitness.rootRotation_action_one
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion

theorem SoficGroups.ThompsonFLocalWitness.rootRotation_action_one :
    PrefixWordAction rootRotation [1] [1, 1] := by sorry
