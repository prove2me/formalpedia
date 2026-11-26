-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_runCost_component_bounds
-- name    : TunnellMap.GloballyRanked.DAState.runCost_component_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:16:18.186653+00:00
-- url     : https://prove2.me/theorems/3ada850a-37ed-456f-8487-786dbcd089ae
-- title:
--   DAState: run Cost component bounds
-- statement:
--   The DAState construction uses the run Cost component bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L83-L98
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L83-L98

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.runCost_component_bounds (st : I.DAState) :
    (st.runCost I).keyComparisons ≤ (st.runCost I).generatorAdvances ∧
      (st.runCost I).queueOperations ≤
        2 * (st.runCost I).generatorAdvances ∧
      (st.runCost I).assignmentWrites ≤
        3 * (st.runCost I).generatorAdvances := by sorry
