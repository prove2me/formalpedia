-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_initial_assignedLast
-- name    : TunnellMap.GloballyRanked.DAState.initial_assignedLast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:01:46.711775+00:00
-- url     : https://prove2.me/theorems/7d648dd5-856d-4f27-ac26-ae968f43ce10
-- title:
--   DAState: initial assigned Last
-- statement:
--   The DAState construction uses the initial assigned Last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L31-L34
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L31-L34

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

theorem TunnellMap.GloballyRanked.DAState.initial_assignedLast (sourceOrder : List S) :
    (initial I sourceOrder).AssignedLast I := by sorry
