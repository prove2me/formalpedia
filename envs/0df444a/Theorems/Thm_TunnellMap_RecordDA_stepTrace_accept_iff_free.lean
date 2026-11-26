-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_stepTrace_accept_iff_free
-- name    : TunnellMap.RecordDA.stepTrace_accept_iff_free
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:39:41.673197+00:00
-- url     : https://prove2.me/theorems/e1d45404-bb2d-405b-b74f-3576853c4e21
-- title:
--   Record DA: step Trace accept iff free
-- statement:
--   **A held-key comparison happens exactly on the non-accepting steps.**  The
--   step compares the proposed key with a held key precisely when the proposed
--   target was already occupied, that is, precisely when the outcome is not
--   `accept`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L183-L186
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L183-L186

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.stepTrace_accept_iff_free (frames : FrameFamily n) {E : DARun n}
    {ev : DAEvent n} {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ev.outcome = DAOutcome.accept ↔ E.held ev.target = none := by sorry
