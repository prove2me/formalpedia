-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_step_eq_none_iff_queue_nil
-- name    : TunnellMap.GloballyRanked.DAState.step_eq_none_iff_queue_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:05.015412+00:00
-- url     : https://prove2.me/theorems/11d58fe4-c550-5733-aa79-169c80e7427e
-- title:
--   DAState: step eq none iff queue nil
-- statement:
--   The DAState construction uses the step eq none iff queue nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L88-L101
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L88-L101

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.step_eq_none_iff_queue_nil
    (hcard : Fintype.card S = Fintype.card T)
    (st : I.DAState) (hv : st.Valid I) :
    st.step I = none ↔ st.queue = [] := by sorry
