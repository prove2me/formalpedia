-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_queued_cursor_lt
-- name    : TunnellMap.GloballyRanked.DAState.queued_cursor_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:09:50.499499+00:00
-- url     : https://prove2.me/theorems/b64bce4e-68b1-54d9-a1dd-262536deb996
-- title:
--   DAState: queued cursor lt
-- statement:
--   A valid queued source has a next untried target.  This is the finite
--   pigeonhole argument in the first paragraph of Theorem 6.3.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L47-L86
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L47-L86

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.queued_cursor_lt (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) (s : S) (hs : s ∈ st.queue) :
    st.cursor s < Fintype.card T := by sorry
