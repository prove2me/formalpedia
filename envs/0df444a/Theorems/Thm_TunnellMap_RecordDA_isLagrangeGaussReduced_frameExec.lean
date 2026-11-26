-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_isLagrangeGaussReduced_frameExec
-- name    : TunnellMap.RecordDA.isLagrangeGaussReduced_frameExec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:36:08.191584+00:00
-- url     : https://prove2.me/theorems/c6badc0f-26c9-4c20-a468-9def3178b1e3
-- title:
--   Record DA: is Lagrange Gauss Reduced frame Exec
-- statement:
--   The computed frame is Lagrange–Gauss reduced.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L63-L65
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L63-L65

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

theorem TunnellMap.RecordDA.isLagrangeGaussReduced_frameExec (hsq : Squarefree n) (s : BResidual n) :
    IsLagrangeGaussReduced (frameExec hsq s) := by sorry
