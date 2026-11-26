-- Prove2me | Theorems.Thm_TunnellMap_targetLiftSign_mem
-- name    : TunnellMap.targetLiftSign_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:47.768341+00:00
-- url     : https://prove2.me/theorems/5de6b603-3808-46a3-a4c8-9674093ba664
-- title:
--   Tunnell Map: target Lift Sign mem
-- statement:
--   The Tunnell Map construction uses the target Lift Sign mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L115-L120
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L115-L120

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.targetLiftSign_mem (v : Triple) :
    targetLiftSign v = 1 ∨ targetLiftSign v = -1 := by sorry
