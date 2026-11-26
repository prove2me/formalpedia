-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_advance
-- name    : TunnellMap.GloballyRanked.DAState.proposalValid_advance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:30.265006+00:00
-- url     : https://prove2.me/theorems/d3be2216-0d02-5ff8-892b-93b70fee77ea
-- title:
--   DAState: proposal Valid advance
-- statement:
--   The DAState construction uses the proposal Valid advance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L199-L213
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L199-L213

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.proposalValid_advance
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T) :
    (st.advance I s rest h).ProposalValid I := by sorry
