-- Prove2me | Theorems.Thm_SoficGroups_MatchedComponentExitBudget_pruned_component_card_tendsto_atTop
-- name    : SoficGroups.MatchedComponentExitBudget.pruned_component_card_tendsto_atTop
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.902902+00:00
-- url     : https://prove2.me/theorems/4fa4a278-9bb1-43b7-b2e7-6139637df736
-- title:
--   SoficGroups.MatchedComponentExitBudget.pruned_component_card_tendsto_atTop
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators

theorem SoficGroups.MatchedComponentExitBudget.pruned_component_card_tendsto_atTop
    (V : ℕ → Type*) [∀ n, Fintype (V n)]
    [∀ n, DecidableEq (V n)]
    (B : (n : ℕ) → Finset (V n))
    (hsize : Tendsto (fun n => Fintype.card (V n)) atTop atTop)
    (hdeleted : Tendsto
      (fun n => ((B n).card : ℝ) / Fintype.card (V n))
      atTop (nhds 0)) :
    Tendsto (fun n => (Finset.univ \ B n : Finset (V n)).card)
      atTop atTop := by sorry
