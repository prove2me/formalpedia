-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_cursorTotal_add_remaining
-- name    : TunnellMap.GloballyRanked.DAState.cursorTotal_add_remaining
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:15:29.674833+00:00
-- url     : https://prove2.me/theorems/17324a03-e774-4517-a6d5-3c5abe2fff1f
-- title:
--   DAState: cursor Total add remaining
-- statement:
--   The DAState construction uses the cursor Total add remaining property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L173-L185
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L173-L185

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

theorem TunnellMap.GloballyRanked.DAState.cursorTotal_add_remaining (st : I.DAState) :
    st.cursorTotal I + st.remaining I =
      Fintype.card S * Fintype.card T := by sorry
