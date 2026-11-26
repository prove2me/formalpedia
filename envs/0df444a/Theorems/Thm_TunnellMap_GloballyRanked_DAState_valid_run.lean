-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_valid_run
-- name    : TunnellMap.GloballyRanked.DAState.valid_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:10:43.903593+00:00
-- url     : https://prove2.me/theorems/15b82f8a-cdbd-521d-ba60-24daa24eccc3
-- title:
--   DAState: valid run
-- statement:
--   The DAState construction uses the valid run property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L358-L366
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceCorrectness.lean#L358-L366

import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
import Definitions.Def_TunnellMap_DeferredAcceptanceCorrectness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.valid_run (st : I.DAState) (hv : st.Valid I) :
    (st.run I).Valid I := by sorry
