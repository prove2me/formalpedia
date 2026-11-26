-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_runWithTrace_run
-- name    : TunnellMap.RecordDA.runWithTrace_run
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:23:49.883176+00:00
-- url     : https://prove2.me/theorems/626ed098-0cae-5e16-82f6-deb6b5dbf42d
-- title:
--   Record DA: run With Trace run
-- statement:
--   **Erasing the trace gives `RecordDA.run`.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L220-L224
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L220-L224

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.runWithTrace_run (hn : 0 ≤ n) (frames : FrameFamily n) (fuel : ℕ)
    (E : DARun n) (hgen : GenStarted E)
    (hstop : (stepK frames (runK frames fuel E)).isNone = true) :
    (runWithTrace frames fuel E).1 = run frames E := by sorry
