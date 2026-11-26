-- Prove2me | Theorems.Thm_TunnellMap_residualTargetLift_injective
-- name    : TunnellMap.residualTargetLift_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:35.644365+00:00
-- url     : https://prove2.me/theorems/e63a6440-725b-5852-97c6-bb991582dfcc
-- title:
--   Tunnell Map: residual Target Lift injective
-- statement:
--   The Tunnell Map construction uses the residual Target Lift injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L399-L411
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L399-L411

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.residualTargetLift_injective {n : ℤ} :
    Function.Injective (residualTargetLift : AResidual n → Triple) := by sorry
