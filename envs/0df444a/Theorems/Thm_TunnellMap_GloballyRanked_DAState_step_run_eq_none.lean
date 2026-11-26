-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_DAState_step_run_eq_none
-- name    : TunnellMap.GloballyRanked.DAState.step_run_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:06:09.915348+00:00
-- url     : https://prove2.me/theorems/3bf4b563-68fc-47da-9397-38c47264b764
-- title:
--   DAState: step run eq none
-- statement:
--   The DAState construction uses the step run eq none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAlgorithm.lean#L186-L193
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/DeferredAcceptanceAlgorithm.lean#L186-L193

import Definitions.Def_TunnellMap_DeferredAcceptance
import Definitions.Def_TunnellMap_PreferenceList
import Definitions.Def_TunnellMap_DeferredAcceptanceAlgorithm
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
open TunnellMap.GloballyRanked.DAState
variable (I : GloballyRanked K S T)

theorem TunnellMap.GloballyRanked.DAState.step_run_eq_none (st : I.DAState) : (st.run I).step I = none := by sorry
