-- Prove2me | Theorems.Thm_TunnellMap_exists_odd_four_mul_iff
-- name    : TunnellMap.exists_odd_four_mul_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:30.552443+00:00
-- url     : https://prove2.me/theorems/7c734335-d23a-579b-bacc-cc46f673cbe3
-- title:
--   Tunnell Map: exists odd four mul iff
-- statement:
--   The Tunnell Map construction uses the exists odd four mul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L17-L25
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L17-L25

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.exists_odd_four_mul_iff (a : ℤ) :
    (∃ q : ℤ, Odd q ∧ a = 4 * q) ↔ a % 8 = 4 := by sorry
