-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_mem_take_after_cursor_advance_cases
-- name    : TunnellMap.GloballyRanked.DAState.mem_take_after_cursor_advance_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:00.984814+00:00
-- url     : https://prove2.me/theorems/e7c028ce-2d24-4ba5-b33a-85334de45b3a
-- title:
--   DAState: mem take after cursor advance cases
-- statement:
--   The DAState construction uses the mem take after cursor advance cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L63-L80
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L63-L80

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.mem_take_after_cursor_advance_cases
    (st st' : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1)
    (hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x)
    {x : S} {t : T}
    (ht : t ∈ (I.preferenceList x).take (st'.cursor x)) :
    t ∈ (I.preferenceList x).take (st.cursor x) ∨
      (x = s ∧ t = st.nextTarget I s h) := by sorry
