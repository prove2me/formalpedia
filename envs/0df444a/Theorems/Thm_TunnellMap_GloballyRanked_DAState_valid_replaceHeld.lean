-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_replaceHeld
-- name    : TunnellMap.GloballyRanked.DAState.valid_replaceHeld
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:35.789669+00:00
-- url     : https://prove2.me/theorems/8e9fa7d9-8403-5cb0-9c8d-7564ea30ef5d
-- title:
--   DAState: valid replace Held
-- statement:
--   The DAState construction uses the valid replace Held property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L225-L331
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L225-L331

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.valid_replaceHeld (st : I.DAState) (hv : st.Valid I)
    (s : S) (rest : List S) (hqueue : st.queue = s :: rest)
    (h : st.cursor s < Fintype.card T) (old : S)
    (hheld : st.held (st.nextTarget I s h) = some old) :
    (st.replaceHeld I s rest h old).Valid I := by sorry
