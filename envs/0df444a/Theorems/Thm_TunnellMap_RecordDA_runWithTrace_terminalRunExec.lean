-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_runWithTrace_terminalRunExec
-- name    : TunnellMap.RecordDA.runWithTrace_terminalRunExec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:25:30.319131+00:00
-- url     : https://prove2.me/theorems/8997ea41-5dbb-46a1-9c6f-2fbdd85f2f2f
-- title:
--   Record DA: run With Trace terminal Run Exec
-- statement:
--   **Erasing the trace of the instrumented executable run gives
--   `terminalRunExec`.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L228-L237
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L228-L237

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.runWithTrace_terminalRunExec (hn : 0 ≤ n) (hsq : Squarefree n)
    (fuel : ℕ)
    (hstop : (stepK (framesExecK hsq)
      (runK (framesExecK hsq) fuel
        (DARun.initial (sourceRosterExec n)))).isNone = true) :
    (runWithTrace (framesExecK hsq) fuel
        (DARun.initial (sourceRosterExec n))).1 =
      terminalRunExec (framesExec hsq) := by sorry
