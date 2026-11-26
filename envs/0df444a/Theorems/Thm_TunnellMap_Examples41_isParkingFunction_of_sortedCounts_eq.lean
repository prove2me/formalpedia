-- Prove2me | Theorems.Thm_TunnellMap_Examples41_isParkingFunction_of_sortedCounts_eq
-- name    : TunnellMap.Examples41.isParkingFunction_of_sortedCounts_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:01.005603+00:00
-- url     : https://prove2.me/theorems/9bffbbf9-8816-5997-b842-6b8208fae66e
-- title:
--   Examples41: is Parking Function of sorted Counts eq
-- statement:
--   Transfer of the parking inequalities along a computed sorted rearrangement.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L129-L135
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L129-L135

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.isParkingFunction_of_sortedCounts_eq {a b : List ℕ}
    (hpos : ∀ x ∈ a, 0 < x) (hb : sortedCounts a = b)
    (hbound : ∀ i : Fin b.length, b.get i ≤ i.1 + 1) :
    IsParkingFunction a := by sorry
