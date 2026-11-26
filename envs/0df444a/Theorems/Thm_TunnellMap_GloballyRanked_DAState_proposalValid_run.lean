-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_proposalValid_run
-- name    : TunnellMap.GloballyRanked.DAState.proposalValid_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:49.214804+00:00
-- url     : https://prove2.me/theorems/5881d403-a939-5d53-820a-6f3faf4e5517
-- title:
--   DAState: proposal Valid run
-- statement:
--   The DAState construction uses the proposal Valid run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L227-L235
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L227-L235

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.proposalValid_run (st : I.DAState) (hv : st.ProposalValid I) :
    (st.run I).ProposalValid I := by sorry
