-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_step
-- name    : TunnellMap.GloballyRanked.DAState.proposalValid_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:34.952331+00:00
-- url     : https://prove2.me/theorems/7e8e60ee-6c5b-5ab0-877b-676fa3ccf2eb
-- title:
--   DAState: proposal Valid step
-- statement:
--   The DAState construction uses the proposal Valid step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L215-L225
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L215-L225

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.proposalValid_step (st st' : I.DAState)
    (hv : st.ProposalValid I) (hstep : st.step I = some st') :
    st'.ProposalValid I := by sorry
