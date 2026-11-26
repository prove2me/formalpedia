-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_valid
-- name    : TunnellMap.GloballyRanked.DAState.initial_valid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:12:12.630606+00:00
-- url     : https://prove2.me/theorems/c47fb251-4dfe-4d0c-8769-201fc142c1e1
-- title:
--   DAState: initial valid
-- statement:
--   The DAState construction uses the initial valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L34-L43
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L34-L43

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.initial_valid (sourceOrder : List S)
    (hnodup : sourceOrder.Nodup) (hcomplete : ∀ s, s ∈ sourceOrder) :
    (initial I sourceOrder).Valid I := by sorry
