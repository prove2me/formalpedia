-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_assigned_matchingOfTerminal
-- name    : TunnellMap.GloballyRanked.DAState.assigned_matchingOfTerminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:34.070629+00:00
-- url     : https://prove2.me/theorems/d873bca8-bfec-5c26-9788-d9566532297f
-- title:
--   DAState: assigned matching Of Terminal
-- statement:
--   The DAState construction uses the assigned matching Of Terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean#L68-L72
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean#L68-L72

import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.assigned_matchingOfTerminal
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = []) (s : S) :
    st.assigned s = some (matchingOfTerminal I hcard st hv hqueue s) := by sorry
