-- Prove2me | Theorems.Thm_TunnellMap_isResidualTargetLift_iff
-- name    : TunnellMap.isResidualTargetLift_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:46:09.832861+00:00
-- url     : https://prove2.me/theorems/c135be4d-75c6-44e6-8b9a-aa24c22958e2
-- title:
--   Tunnell Map: is Residual Target Lift iff
-- statement:
--   The Tunnell Map construction uses the is Residual Target Lift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L67-L89
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L67-L89

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.isResidualTargetLift_iff (n : ℤ) (v : Triple) :
    IsResidualTargetLift n v ↔ ∃ t : AResidual n, residualTargetLift t = v := by sorry
