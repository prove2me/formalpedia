-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_stepTrace_shape
-- name    : TunnellMap.RecordDA.stepTrace_shape
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:12:04.379074+00:00
-- url     : https://prove2.me/theorems/c313db95-8dfb-5b22-b8f4-de4a3197882c
-- title:
--   Record DA: step Trace shape
-- statement:
--   The Record DA construction uses the step Trace shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L127-L165
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/RecordTrace.lean#L127-L165

import Definitions.Def_TunnellMap_KernelPipeline
import Definitions.Def_TunnellMap_RecordTrace
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.stepTrace_shape (frames : FrameFamily n) {E : DARun n} {ev : DAEvent n}
    {E' : DARun n} (h : stepTrace frames E = some (ev, E')) :
    ∃ (s : BResidual n) (rest : List (BResidual n)) (g : GenState),
      E.queue = s :: rest ∧ s ∈ E.sources ∧
      BlockGen.advanceK s (frames s) (E.gen s) =
        some (⟨ev.key, ev.target, ev.sign⟩, g) ∧
      ev.proposer = s ∧ E'.gen = Function.update E.gen s g ∧
      (ev.outcome = DAOutcome.accept ↔ E.held ev.target = none) := by sorry
