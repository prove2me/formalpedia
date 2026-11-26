-- Prove2me | Theorems.Thm_TunnellMap_residualTargetLift_neg
-- name    : TunnellMap.residualTargetLift_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:46.125814+00:00
-- url     : https://prove2.me/theorems/bdd8e36e-3e50-5a20-a32f-0a08c9e5c60c
-- title:
--   Tunnell Map: residual Target Lift neg
-- statement:
--   The Tunnell Map construction uses the residual Target Lift neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L413-L415
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L413-L415

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.residualTargetLift_neg {n : ℤ} (t : AResidual n) :
    residualTargetLift (negAResidual t) = negTriple (residualTargetLift t) := by sorry
