-- Prove2me | Theorems.Thm_TunnellMap_Examples41_parking_rearrangement41
-- name    : TunnellMap.Examples41.parking_rearrangement41
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:22:10.642168+00:00
-- url     : https://prove2.me/theorems/441d872f-0678-5bf6-8078-e036550fd160
-- title:
--   Examples41: parking rearrangement41
-- statement:
--   The Examples41 construction uses the parking rearrangement41 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L143-L150
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L143-L150

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.parking_rearrangement41 :
    sortedCounts [1, 3, 1, 1] = [1, 1, 1, 3] ∧
      IsParkingFunction [1, 3, 1, 1] ∧
      1 + 3 + 1 + 1 = 6 ∧
      6 ≤ 4 * (4 + 1) / 2 := by sorry
