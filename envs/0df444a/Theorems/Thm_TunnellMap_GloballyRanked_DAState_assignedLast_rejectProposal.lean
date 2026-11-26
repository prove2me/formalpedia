-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_assignedLast_rejectProposal
-- name    : TunnellMap.GloballyRanked.DAState.assignedLast_rejectProposal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:01:50.457259+00:00
-- url     : https://prove2.me/theorems/13587e06-b7de-5054-8726-8465d841d710
-- title:
--   DAState: assigned Last reject Proposal
-- statement:
--   The DAState construction uses the assigned Last reject Proposal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L55-L68
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAccounting.lean#L55-L68

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

theorem TunnellMap.GloballyRanked.DAState.assignedLast_rejectProposal (st : I.DAState)
    (hv : st.Valid I) (hlast : st.AssignedLast I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) :
    (st.rejectProposal I s rest h).AssignedLast I := by sorry
