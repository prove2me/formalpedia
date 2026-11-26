-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_replaceHeld
-- name    : TunnellMap.GloballyRanked.DAState.proposalValid_replaceHeld
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:06.163949+00:00
-- url     : https://prove2.me/theorems/fef2021c-b125-5bf3-8e0b-2446d99e0777
-- title:
--   DAState: proposal Valid replace Held
-- statement:
--   The DAState construction uses the proposal Valid replace Held property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L150-L197
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L150-L197

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.proposalValid_replaceHeld
    (st : I.DAState) (hv : st.ProposalValid I)
    (s : S) (rest : List S) (h : st.cursor s < Fintype.card T)
    (old : S) (hheld : st.held (st.nextTarget I s h) = some old)
    (hbetter : I.rank s (st.nextTarget I s h) <
      I.rank old (st.nextTarget I s h)) :
    (st.replaceHeld I s rest h old).ProposalValid I := by sorry
