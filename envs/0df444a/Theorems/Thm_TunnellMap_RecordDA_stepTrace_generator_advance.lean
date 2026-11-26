-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_stepTrace_generator_advance
-- name    : TunnellMap.RecordDA.stepTrace_generator_advance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:38:24.02952+00:00
-- url     : https://prove2.me/theorems/0e9d9c16-3553-50a2-9a44-3d52098f80d3
-- title:
--   Record DA: step Trace generator advance
-- statement:
--   **One generator advance per event.**  The record carried by an event is
--   exactly the record the proposer's generator emitted on that step, and the
--   proposer's generator is the only one that moved.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L171-L177
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L171-L177

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.stepTrace_generator_advance (frames : FrameFamily n) {E : DARun n}
    {ev : DAEvent n} {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ∃ g, BlockGen.advanceK ev.proposer (frames ev.proposer) (E.gen ev.proposer) =
        some (⟨ev.key, ev.target, ev.sign⟩, g) ∧
      E'.gen = Function.update E.gen ev.proposer g := by sorry
