-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_advance
-- name    : TunnellMap.GloballyRanked.DAState.assignedLast_advance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:02:21.08339+00:00
-- url     : https://prove2.me/theorems/bc779217-6f4b-544e-b0bc-eef18898bc81
-- title:
--   DAState: assigned Last advance
-- statement:
--   The DAState construction uses the assigned Last advance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L107-L118
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L107-L118

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

theorem TunnellMap.GloballyRanked.DAState.assignedLast_advance (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).AssignedLast I := by sorry
