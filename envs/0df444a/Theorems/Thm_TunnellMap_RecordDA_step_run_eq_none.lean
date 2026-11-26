-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_step_run_eq_none
-- name    : TunnellMap.RecordDA.step_run_eq_none
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:59:43.760827+00:00
-- url     : https://prove2.me/theorems/f9310373-ef28-571d-b2be-e12dd1db6589
-- title:
--   Record DA: step run eq none
-- statement:
--   The Record DA construction uses the step run eq none property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptance.lean#L226-L230
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordDeferredAcceptance.lean#L226-L230

import Definitions.Def_TunnellMap_BlockGeneratorState
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_RecordDeferredAcceptance
import Theorems.Thm_TunnellMap_GloballyRanked_DAState_step_run_eq_none

set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}
variable {frames : FrameFamily n} {E : DARun n} {s old : BResidual n}
  {rest : List (BResidual n)} {r rold : IncidentRecord} {g : GenState}

theorem TunnellMap.RecordDA.step_run_eq_none (frames : FrameFamily n) (E : DARun n) :
    step frames (run frames E) = none := by sorry
