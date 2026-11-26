-- Prove2me | Theorems.Thm_TunnellMap_isParkingFunction_of_indexed_bounds
-- name    : TunnellMap.isParkingFunction_of_indexed_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:44:46.136026+00:00
-- url     : https://prove2.me/theorems/bc62fb46-03ef-489b-b631-6c8a30a4e70f
-- title:
--   Tunnell Map: is Parking Function of indexed bounds
-- statement:
--   If some enumeration satisfies the parking inequalities, then the sorted
--   rearrangement does as well.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingRearrangement.lean#L27-L92
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingRearrangement.lean#L27-L92

import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_ParkingRearrangement
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.isParkingFunction_of_indexed_bounds (a : List ℕ)
    (hpos : ∀ x ∈ a, 0 < x)
    (hbound : ∀ i : Fin a.length, a.get i ≤ i.1 + 1) :
    IsParkingFunction a := by sorry
