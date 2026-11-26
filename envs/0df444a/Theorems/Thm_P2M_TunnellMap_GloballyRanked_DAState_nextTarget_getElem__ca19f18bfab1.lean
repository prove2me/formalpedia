-- Prove2me | Theorems.Thm_P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1
-- name    : P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:12.442246+00:00
-- url     : https://prove2.me/theorems/09201796-a4f1-53a3-a184-ac0bf18abed2
-- title:
--   P2 M Tunnell Map Globally Ranked DAState next Target get Elem  ca19f18bfab1: P2 M Tunnell Map Globally Ranked DAState next Target get Elem  ca19f18bfab1
-- statement:
--   The P2 M Tunnell Map Globally Ranked DAState next Target get Elem  ca19f18bfab1 construction uses the P2 M Tunnell Map Globally Ranked DAState next Target get Elem  ca19f18bfab1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L103-L108
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L103-L108

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1 (st : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T) :
    (I.preferenceList s)[st.cursor s]? = some (st.nextTarget I s h) := by sorry

alias «TunnellMap».«GloballyRanked».«DAState».«nextTarget_getElem?» := P2M_TunnellMap_GloballyRanked_DAState_nextTarget_getElem__ca19f18bfab1
