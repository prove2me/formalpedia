-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_oneStepCost_bounds
-- name    : TunnellMap.GloballyRanked.DAState.oneStepCost_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:02:11.777957+00:00
-- url     : https://prove2.me/theorems/83b03b47-98e5-44bb-91d0-d04b4956995d
-- title:
--   DAState: one Step Cost bounds
-- statement:
--   The DAState construction uses the one Step Cost bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L58-L73
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L58-L73

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.oneStepCost_bounds (st st' : I.DAState)
    (hstep : st.step I = some st') :
    (st.oneStepCost I).generatorAdvances = 1 ∧
      (st.oneStepCost I).keyComparisons ≤ 1 ∧
      (st.oneStepCost I).queueOperations ≤ 2 ∧
      (st.oneStepCost I).assignmentWrites ≤ 3 := by sorry
