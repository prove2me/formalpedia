-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_matchingOfTerminal_apply
-- name    : TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:05.094343+00:00
-- url     : https://prove2.me/theorems/630636d9-a5cf-4e4e-9bbc-18b610b89b06
-- title:
--   DAState: matching Of Terminal apply
-- statement:
--   The DAState construction uses the matching Of Terminal apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean#L62-L66
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean#L62-L66

import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = []) (s : S) :
    matchingOfTerminal I hcard st hv hqueue s =
      assignedTarget I st hv hqueue s := by sorry

attribute [defeq] TunnellMap.GloballyRanked.DAState.matchingOfTerminal_apply
