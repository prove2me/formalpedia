-- Prove2me | Theorems.Thm_TunnellMap_negTriple_residualTargetLift
-- name    : TunnellMap.negTriple_residualTargetLift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:47:59.535694+00:00
-- url     : https://prove2.me/theorems/aec71971-fb88-4322-8886-db3c1649f699
-- title:
--   Tunnell Map: neg Triple residual Target Lift
-- statement:
--   The Tunnell Map construction uses the neg Triple residual Target Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L122-L125
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L122-L125

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.negTriple_residualTargetLift {n : ℤ} (t : AResidual n) :
    negTriple (residualTargetLift t) = residualTargetLift (negAResidual t) := by sorry
