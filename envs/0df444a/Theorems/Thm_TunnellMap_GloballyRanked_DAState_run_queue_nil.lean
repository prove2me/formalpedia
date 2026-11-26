-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_run_queue_nil
-- name    : TunnellMap.GloballyRanked.DAState.run_queue_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:09.021348+00:00
-- url     : https://prove2.me/theorems/9853b074-5aa7-5590-aa4d-0e0358a88285
-- title:
--   DAState: run queue nil
-- statement:
--   From a valid state on equal finite sides, `run` terminates with no free
--   source left in the FIFO queue.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L370-L375
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L370-L375

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.run_queue_nil (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    (st.run I).queue = [] := by sorry
