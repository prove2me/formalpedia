-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_old_mem_take_after_cursor_advance
-- name    : TunnellMap.GloballyRanked.DAState.old_mem_take_after_cursor_advance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:34:29.95284+00:00
-- url     : https://prove2.me/theorems/0e9a0d79-95ba-4339-870a-ceb6621db574
-- title:
--   DAState: old mem take after cursor advance
-- statement:
--   The DAState construction uses the old mem take after cursor advance property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L38-L52
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceStability.lean#L38-L52

import Definitions.Def_TunnellMap_DeferredAcceptanceOutput
import Definitions.Def_TunnellMap_DeferredAcceptanceStability
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.old_mem_take_after_cursor_advance
    (st st' : I.DAState) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1)
    (hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x)
    {x : S} {t : T}
    (ht : t ∈ (I.preferenceList x).take (st.cursor x)) :
    t ∈ (I.preferenceList x).take (st'.cursor x) := by sorry
