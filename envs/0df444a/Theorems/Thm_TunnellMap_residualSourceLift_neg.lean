-- Prove2me | Theorems.Thm_TunnellMap_residualSourceLift_neg
-- name    : TunnellMap.residualSourceLift_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:42.798229+00:00
-- url     : https://prove2.me/theorems/1d7b287c-8774-5092-9dec-6c00291302f9
-- title:
--   Tunnell Map: residual Source Lift neg
-- statement:
--   The Tunnell Map construction uses the residual Source Lift neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L431-L433
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L431-L433

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.residualSourceLift_neg {n : ℤ} (s : BResidual n) :
    residualSourceLift (negBResidual s) = negTriple (residualSourceLift s) := by sorry
