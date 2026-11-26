-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_rejectProposal
-- name    : TunnellMap.GloballyRanked.DAState.proposalValid_rejectProposal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:14.073792+00:00
-- url     : https://prove2.me/theorems/dc79d6c8-c087-4471-843a-bd1620873096
-- title:
--   DAState: proposal Valid reject Proposal
-- statement:
--   The DAState construction uses the proposal Valid reject Proposal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L120-L148
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L120-L148

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.proposalValid_rejectProposal
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T)
    {old : S} (hheld : st.held (st.nextTarget I s h) = some old)
    (hnotbetter : ¬ I.rank s (st.nextTarget I s h) <
      I.rank old (st.nextTarget I s h)) :
    (st.rejectProposal I s rest h).ProposalValid I := by sorry
