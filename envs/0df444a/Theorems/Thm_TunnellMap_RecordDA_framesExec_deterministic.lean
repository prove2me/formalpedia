-- Prove2me | Theorems.Thm_TunnellMap_RecordDA_framesExec_deterministic
-- name    : TunnellMap.RecordDA.framesExec_deterministic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:36:18.432683+00:00
-- url     : https://prove2.me/theorems/d5ab055c-80fe-5716-81be-dc8fd6a52be4
-- title:
--   Record DA: frames Exec deterministic
-- statement:
--   The computed frame family is deterministic: it does not depend on the
--   proof of squarefreeness.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L69-L70
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputablePipeline.lean#L69-L70

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

theorem TunnellMap.RecordDA.framesExec_deterministic (hsq hsq' : Squarefree n) :
    framesExec hsq = framesExec hsq' := by sorry
