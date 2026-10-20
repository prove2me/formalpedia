-- Prove2me | Theorems.Thm_SoficGroups_RankArcCharging_card_sdiff_selectedRankSupport
-- name    : SoficGroups.RankArcCharging.card_sdiff_selectedRankSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/5de73030-3806-4875-935c-d33418bae90d
-- title:
--   SoficGroups.RankArcCharging.card_sdiff_selectedRankSupport
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

theorem SoficGroups.RankArcCharging.card_sdiff_selectedRankSupport
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ) :
    (U \ selectedRankSupport P b j).card =
      ∑ C ∈ P.parts,
        (C.card - (C.filter fun x => b x = j C).card) := by sorry
