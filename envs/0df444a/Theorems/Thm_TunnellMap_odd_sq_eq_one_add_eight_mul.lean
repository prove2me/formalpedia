-- Prove2me | Theorems.Thm_TunnellMap_odd_sq_eq_one_add_eight_mul
-- name    : TunnellMap.odd_sq_eq_one_add_eight_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:18.150561+00:00
-- url     : https://prove2.me/theorems/004fa3c0-031d-4643-826f-f8506b8e83b1
-- title:
--   Tunnell Map: odd sq eq one add eight mul
-- statement:
--   The Tunnell Map construction uses the odd sq eq one add eight mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L35-L43
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Midpoint.lean#L35-L43

import Definitions.Def_TunnellMap_QuarterTurns
import Definitions.Def_TunnellMap_Midpoint
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.odd_sq_eq_one_add_eight_mul {x : ℤ} (hx : Odd x) :
    ∃ k : ℤ, x ^ 2 = 1 + 8 * k := by sorry
