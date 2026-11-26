-- Prove2me | Theorems.Thm_TunnellMap_residualSourceLift_injective
-- name    : TunnellMap.residualSourceLift_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:26:48.347042+00:00
-- url     : https://prove2.me/theorems/4cd9f7b6-2fb1-4bdb-b1c9-56b6bab6916e
-- title:
--   Tunnell Map: residual Source Lift injective
-- statement:
--   The Tunnell Map construction uses the residual Source Lift injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L417-L429
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L417-L429

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.residualSourceLift_injective {n : ℤ} :
    Function.Injective (residualSourceLift : BResidual n → Triple) := by sorry
