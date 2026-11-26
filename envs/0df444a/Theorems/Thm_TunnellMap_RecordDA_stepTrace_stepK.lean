-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_stepTrace_stepK
-- name    : TunnellMap.RecordDA.stepTrace_stepK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:12:28.5036+00:00
-- url     : https://prove2.me/theorems/bc1a8fa0-3aee-4650-9c38-cf33847c730a
-- title:
--   Record DA: step Trace step K
-- statement:
--   **Erasing the instrumentation of one step gives `RecordDA.stepK`.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L91-L113
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L91-L113

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.stepTrace_stepK (frames : FrameFamily n) (E : DARun n) :
    (stepTrace frames E).map Prod.snd = stepK frames E := by sorry
