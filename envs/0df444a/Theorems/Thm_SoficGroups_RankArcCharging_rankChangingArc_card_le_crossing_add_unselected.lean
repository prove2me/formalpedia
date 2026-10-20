-- Prove2me | Theorems.Thm_SoficGroups_RankArcCharging_rankChangingArc_card_le_crossing_add_unselected
-- name    : SoficGroups.RankArcCharging.rankChangingArc_card_le_crossing_add_unselected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/afbafe13-dd8d-4864-a4a5-01b734808c0e
-- title:
--   SoficGroups.RankArcCharging.rankChangingArc_card_le_crossing_add_unselected
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
open SoficGroups.RankArcCharging
open scoped BigOperators

theorem SoficGroups.RankArcCharging.rankChangingArc_card_le_crossing_add_unselected
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ)
    (w : Equiv.Perm V) :
    (rankChangingArc U b w).card ≤
      (partitionWordCrossing P w).card +
        2 * (U \ selectedRankSupport P b j).card := by sorry
