-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_frameExecK_eq
-- name    : TunnellMap.RecordDA.frameExecK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:09:05.982618+00:00
-- url     : https://prove2.me/theorems/b0d2ac18-5f54-5c8b-9000-f6153f8cee53
-- title:
--   Record DA: frame Exec K eq
-- statement:
--   The Record DA construction uses the frame Exec K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean#L87-L88
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelPipeline.lean#L87-L88

import Definitions.Def_TunnellMap_KernelGenerator
import Definitions.Def_TunnellMap_ComputablePipeline
import Definitions.Def_TunnellMap_KernelPipeline
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.frameExecK_eq (hsq : Squarefree n) (s : BResidual n) :
    frameExecK hsq s = frameExec hsq s := by sorry
