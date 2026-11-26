-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_runCost_advances_add_remaining
-- name    : TunnellMap.GloballyRanked.DAState.runCost_advances_add_remaining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:15:49.995466+00:00
-- url     : https://prove2.me/theorems/ab4fb82d-bd1a-5588-a263-177311441932
-- title:
--   DAState: run Cost advances add remaining
-- statement:
--   The DAState construction uses the run Cost advances add remaining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L100-L112
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ControlCost.lean#L100-L112

import Definitions.Def_TunnellMap_DeferredAcceptanceAccounting
import Definitions.Def_TunnellMap_ControlCost
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.runCost_advances_add_remaining (st : I.DAState) :
    (st.runCost I).generatorAdvances + (st.run I).remaining I =
      st.remaining I := by sorry
