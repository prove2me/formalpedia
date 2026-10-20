-- Prove2me | Theorems.Thm_SoficGroups_RankArcCharging_selectedRankSupport_rank_eq
-- name    : SoficGroups.RankArcCharging.selectedRankSupport_rank_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/9857f94b-5fee-4159-845f-48882c88d54d
-- title:
--   SoficGroups.RankArcCharging.selectedRankSupport_rank_eq
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

theorem SoficGroups.RankArcCharging.selectedRankSupport_rank_eq
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (b : V → ℤ) (j : Finset V → ℤ)
    {x : V} (hx : x ∈ selectedRankSupport P b j) :
    b x = j (P.part x) := by sorry
