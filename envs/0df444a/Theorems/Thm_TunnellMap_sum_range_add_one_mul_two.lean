-- Prove2me | Theorems.Thm_TunnellMap_sum_range_add_one_mul_two
-- name    : TunnellMap.sum_range_add_one_mul_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:02:20.926389+00:00
-- url     : https://prove2.me/theorems/4f0a9a2a-832d-42cf-9b58-6b266e36d4a4
-- title:
--   Tunnell Map: sum range add one mul two
-- statement:
--   The Tunnell Map construction uses the sum range add one mul two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingTotal.lean#L12-L18
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingTotal.lean#L12-L18

import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_ParkingTotal
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.sum_range_add_one_mul_two (m : ℕ) :
    (Finset.sum (Finset.range m) fun i => i + 1) * 2 = m * (m + 1) := by sorry
