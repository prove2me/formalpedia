-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalSteps_initial_eq_terminalCursorTotal
-- name    : TunnellMap.GloballyRanked.DAState.proposalSteps_initial_eq_terminalCursorTotal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:15:00.707219+00:00
-- url     : https://prove2.me/theorems/a3b36bb1-642f-5def-8368-8e74e41c79b5
-- title:
--   DAState: proposal Steps initial eq terminal Cursor Total
-- statement:
--   The DAState construction uses the proposal Steps initial eq terminal Cursor Total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L203-L216
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L203-L216

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

theorem TunnellMap.GloballyRanked.DAState.proposalSteps_initial_eq_terminalCursorTotal
    (sourceOrder : List S) :
    (initial I sourceOrder).proposalSteps I =
      ((initial I sourceOrder).run I).cursorTotal I := by sorry
