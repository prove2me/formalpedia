-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_tried_occupied_after_cursor_advance
-- name    : TunnellMap.GloballyRanked.DAState.tried_occupied_after_cursor_advance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:11:07.285701+00:00
-- url     : https://prove2.me/theorems/c67416ce-a9fc-49a5-92b9-2a394dd63e30
-- title:
--   DAState: tried occupied after cursor advance
-- statement:
--   The cursor/occupancy part of the invariant is common to all three
--   proposal outcomes.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L112-L130
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L112-L130

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.tried_occupied_after_cursor_advance
    (st st' : I.DAState) (hv : st.Valid I) (s : S)
    (h : st.cursor s < Fintype.card T)
    (hself : st'.cursor s = st.cursor s + 1)
    (hother : ∀ x, x ≠ s → st'.cursor x = st.cursor x)
    (hmono : ∀ t, st.Occupied I t → st'.Occupied I t)
    (hnext : st'.Occupied I (st.nextTarget I s h)) :
    ∀ x t, t ∈ (I.preferenceList x).take (st'.cursor x) →
      st'.Occupied I t := by sorry
