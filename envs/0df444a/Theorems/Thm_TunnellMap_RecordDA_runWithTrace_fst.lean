-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_runWithTrace_fst
-- name    : TunnellMap.RecordDA.runWithTrace_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:25:21.932596+00:00
-- url     : https://prove2.me/theorems/4118a874-da54-434e-aa22-37913f98edfd
-- title:
--   Record DA: run With Trace fst
-- statement:
--   **Erasing the trace gives the fuel-driven run.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L201-L217
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L201-L217

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.runWithTrace_fst (frames : FrameFamily n) :
    ∀ (fuel : ℕ) (E : DARun n), (runWithTrace frames fuel E).1 = runK frames fuel E := by sorry
