-- Prove2me | Theorems.Thm_SoficGroups_sum_card_inter_partition
-- name    : SoficGroups.sum_card_inter_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/97be1c05-bc5d-4240-8ed2-b2da5f692c1f
-- title:
--   SoficGroups.sum_card_inter_partition
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff

theorem SoficGroups.sum_card_inter_partition {α : Type*} [DecidableEq α]
    {U : Finset α} (P : Finpartition U) (B : Finset α) :
    ∑ C ∈ P.parts, (C ∩ B).card = (U ∩ B).card := by sorry
