-- Prove2me | Theorems.Thm_SoficGroups_CompletedSourceFinalGeneratorTransfer_surviving_card_ratio_tendsto_one
-- name    : SoficGroups.CompletedSourceFinalGeneratorTransfer.surviving_card_ratio_tendsto_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/6a52a2ce-ba93-4925-993b-8c0ab32460ac
-- title:
--   SoficGroups.CompletedSourceFinalGeneratorTransfer.surviving_card_ratio_tendsto_one
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer

theorem SoficGroups.CompletedSourceFinalGeneratorTransfer.surviving_card_ratio_tendsto_one
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (D : (n : ℕ) → Finset (V n))
    (hZ : ∀ n, (Finset.univ \ D n : Finset (V n)).Nonempty)
    (hdeleted : Tendsto
      (fun n => ((D n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto
      (fun n =>
        (((Finset.univ \ D n : Finset (V n)).card : ℝ) /
          Fintype.card (V n)))
      atTop (nhds 1) := by sorry
