-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_framesExec_apply
-- name    : TunnellMap.RecordDA.framesExec_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:08:53.964225+00:00
-- url     : https://prove2.me/theorems/2563c02a-95a3-47e2-b3a8-d31abd3a4e57
-- title:
--   Record DA: frames Exec apply
-- statement:
--   The Record DA construction uses the frames Exec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L59-L60
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L59-L60

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_InverseByRerun
import Definitions.Def_TunnellMap_LagrangeGauss
import Definitions.Def_TunnellMap_DeterministicFrame
import Definitions.Def_TunnellMap_ComputablePipeline
set_option autoImplicit true
open TunnellMap
open TunnellMap.RecordDA
open OrderedGenerator BlockGen
variable {n : ℤ}

theorem TunnellMap.RecordDA.framesExec_apply (hsq : Squarefree n) (s : BResidual n) :
    framesExec hsq s = frameExec hsq s := by sorry

attribute [defeq] TunnellMap.RecordDA.framesExec_apply
