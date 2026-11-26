-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_terminal_cursor_eq_proposalCount
-- name    : TunnellMap.GloballyRanked.DAState.terminal_cursor_eq_proposalCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:15:05.948713+00:00
-- url     : https://prove2.me/theorems/bbb1ca64-b627-4b08-96a7-65bcdc3b14df
-- title:
--   DAState: terminal cursor eq proposal Count
-- statement:
--   At a valid terminal state, every cursor is exactly the proposal count of
--   the extracted perfect matching.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L147-L167
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L147-L167

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

theorem TunnellMap.GloballyRanked.DAState.terminal_cursor_eq_proposalCount
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hlast : st.AssignedLast I)
    (hqueue : st.queue = []) (s : S) :
    st.cursor s =
      I.proposalCount (matchingOfTerminal I hcard st hv hqueue) s := by sorry
