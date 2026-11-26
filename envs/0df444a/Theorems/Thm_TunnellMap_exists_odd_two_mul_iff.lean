-- Prove2me | Theorems.Thm_TunnellMap_exists_odd_two_mul_iff
-- name    : TunnellMap.exists_odd_two_mul_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:45:57.535648+00:00
-- url     : https://prove2.me/theorems/ae2d5f28-e988-42d5-91c1-a8b0fb325fc7
-- title:
--   Tunnell Map: exists odd two mul iff
-- statement:
--   The Tunnell Map construction uses the exists odd two mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L27-L35
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L27-L35

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.exists_odd_two_mul_iff (a : ℤ) :
    (∃ q : ℤ, Odd q ∧ a = 2 * q) ↔ a % 4 = 2 := by sorry
