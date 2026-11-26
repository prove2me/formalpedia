-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_stepTrace_step
-- name    : TunnellMap.RecordDA.stepTrace_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:38:01.142908+00:00
-- url     : https://prove2.me/theorems/149c16d3-3480-5bc5-9ca2-29491007275e
-- title:
--   Record DA: step Trace step
-- statement:
--   **Erasing the instrumentation of one step gives `RecordDA.step`.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L116-L119
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L116-L119

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.stepTrace_step (hn : 0 ≤ n) (frames : FrameFamily n) {E : DARun n}
    (hgen : GenStarted E) :
    (stepTrace frames E).map Prod.snd = step frames E := by sorry
