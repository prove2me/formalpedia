-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_terminal_cursorTotal_eq_proposalCount_sum
-- name    : TunnellMap.GloballyRanked.DAState.terminal_cursorTotal_eq_proposalCount_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:15:10.125459+00:00
-- url     : https://prove2.me/theorems/a9a8c55b-eb79-5f2f-b759-06ef3b0a9670
-- title:
--   DAState: terminal cursor Total eq proposal Count sum
-- statement:
--   The actual terminal cursor sum equals the abstract proposal-count sum of
--   the output matching.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L220-L230
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L220-L230

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

theorem TunnellMap.GloballyRanked.DAState.terminal_cursorTotal_eq_proposalCount_sum
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hlast : st.AssignedLast I)
    (hqueue : st.queue = []) :
    st.cursorTotal I =
      ∑ s : S, I.proposalCount
        (matchingOfTerminal I hcard st hv hqueue) s := by sorry
