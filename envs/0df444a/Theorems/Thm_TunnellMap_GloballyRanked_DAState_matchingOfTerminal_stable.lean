-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_stable
-- name    : TunnellMap.GloballyRanked.DAState.matchingOfTerminal_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:35:53.823036+00:00
-- url     : https://prove2.me/theorems/a59f93ce-8089-40d0-ab36-dcada8f0e499
-- title:
--   DAState: matching Of Terminal stable
-- statement:
--   The DAState construction uses the matching Of Terminal stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L292-L298
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L292-L298

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.matchingOfTerminal_stable
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hp : st.ProposalValid I)
    (hqueue : st.queue = []) :
    I.Stable (matchingOfTerminal I hcard st hv hqueue) := by sorry
