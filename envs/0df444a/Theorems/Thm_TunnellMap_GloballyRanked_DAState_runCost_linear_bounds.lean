-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_runCost_linear_bounds
-- name    : TunnellMap.GloballyRanked.DAState.runCost_linear_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:48:36.475846+00:00
-- url     : https://prove2.me/theorems/3d0947b3-c38e-5eb2-8b8e-155aaa2305a2
-- title:
--   DAState: run Cost linear bounds
-- statement:
--   Exact constants implying the `O(N)` operation statement in Theorem 7.3.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L123-L131
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L123-L131

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.runCost_linear_bounds (st : I.DAState) :
    (st.runCost I).generatorAdvances = st.proposalSteps I ∧
      (st.runCost I).keyComparisons ≤ st.proposalSteps I ∧
      (st.runCost I).queueOperations ≤ 2 * st.proposalSteps I ∧
      (st.runCost I).assignmentWrites ≤ 3 * st.proposalSteps I := by sorry
