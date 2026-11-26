-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_run_proposalSteps_le_triangular
-- name    : TunnellMap.GloballyRanked.DAState.run_proposalSteps_le_triangular
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:47:53.991224+00:00
-- url     : https://prove2.me/theorems/a8875038-56ad-4c19-9985-792d48433e5c
-- title:
--   DAState: run proposal Steps le triangular
-- statement:
--   Exact proposal accounting and the paper's triangular upper bound for a
--   complete FIFO run.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L234-L255
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L234-L255

import Definitions.Def_TunnellMap_DeferredAcceptanceStability
import Definitions.Def_TunnellMap_PreferenceListPosition
import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.run_proposalSteps_le_triangular
    (hcard : Fintype.card S = Fintype.card T)
    (sourceOrder : List S) (hnodup : sourceOrder.Nodup)
    (hcomplete : ∀ s, s ∈ sourceOrder) :
    (initial I sourceOrder).proposalSteps I ≤
      Fintype.card S * (Fintype.card S + 1) / 2 := by sorry
