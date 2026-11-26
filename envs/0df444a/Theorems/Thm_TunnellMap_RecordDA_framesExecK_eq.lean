-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_framesExecK_eq
-- name    : TunnellMap.RecordDA.framesExecK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:11:51.421748+00:00
-- url     : https://prove2.me/theorems/c16f1122-f518-4749-8e53-c7ac24d1a257
-- title:
--   Record DA: frames Exec K eq
-- statement:
--   The Record DA construction uses the frames Exec K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean#L90-L91
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean#L90-L91

import Definitions.Def_TunnellMap_KernelGenerator
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_KernelPipeline
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.framesExecK_eq (hsq : Squarefree n) : framesExecK hsq = framesExec hsq := by sorry
