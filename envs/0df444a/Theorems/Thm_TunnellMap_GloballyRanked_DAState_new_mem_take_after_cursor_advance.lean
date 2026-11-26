-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_new_mem_take_after_cursor_advance
-- name    : TunnellMap.GloballyRanked.DAState.new_mem_take_after_cursor_advance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:33:53.290961+00:00
-- url     : https://prove2.me/theorems/217832e1-42c4-42fc-a749-65cdf86f5a1a
-- title:
--   DAState: new mem take after cursor advance
-- statement:
--   The DAState construction uses the new mem take after cursor advance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L54-L61
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L54-L61

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.new_mem_take_after_cursor_advance
    (st st' : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1) :
    st.nextTarget I s h ∈
      (I.preferenceList s).take (st'.cursor s) := by sorry
