-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_acceptEmpty
-- name    : TunnellMap.GloballyRanked.DAState.assignedLast_acceptEmpty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:01:37.251928+00:00
-- url     : https://prove2.me/theorems/b7fec7a0-8107-55ef-b5e7-0d38a6638858
-- title:
--   DAState: assigned Last accept Empty
-- statement:
--   The DAState construction uses the assigned Last accept Empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L36-L53
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L36-L53

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

theorem TunnellMap.GloballyRanked.DAState.assignedLast_acceptEmpty (st : I.DAState)
    (hlast : st.AssignedLast I) (s : S) (rest : List S)
    (h : st.cursor s < Fintype.card T) :
    (st.acceptEmpty I s rest h).AssignedLast I := by sorry
