-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_held_iff_matchingOfTerminal
-- name    : TunnellMap.GloballyRanked.DAState.held_iff_matchingOfTerminal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:28:39.71383+00:00
-- url     : https://prove2.me/theorems/b4cf6b9e-44b5-56d7-8ab2-34614ea84297
-- title:
--   DAState: held iff matching Of Terminal
-- statement:
--   The DAState construction uses the held iff matching Of Terminal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean#L74-L87
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceOutput.lean#L74-L87

import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.held_iff_matchingOfTerminal
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (hqueue : st.queue = [])
    (s : S) (t : T) :
    st.held t = some s ↔ matchingOfTerminal I hcard st hv hqueue s = t := by sorry
