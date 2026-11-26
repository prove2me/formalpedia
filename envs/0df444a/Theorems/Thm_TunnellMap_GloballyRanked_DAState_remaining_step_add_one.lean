-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_remaining_step_add_one
-- name    : TunnellMap.GloballyRanked.DAState.remaining_step_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:14:34.433971+00:00
-- url     : https://prove2.me/theorems/fa473011-862f-595c-a40a-6f9d9f1b36b1
-- title:
--   DAState: remaining step add one
-- statement:
--   The DAState construction uses the remaining step add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L187-L197
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L187-L197

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

theorem TunnellMap.GloballyRanked.DAState.remaining_step_add_one (st st' : I.DAState)
    (hstep : st.step I = some st') :
    st'.remaining I + 1 = st.remaining I := by sorry
