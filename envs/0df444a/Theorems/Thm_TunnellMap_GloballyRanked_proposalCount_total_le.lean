-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_total_le
-- name    : TunnellMap.GloballyRanked.proposalCount_total_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:01:14.321856+00:00
-- url     : https://prove2.me/theorems/32785f5f-eaa8-4b25-98f0-3865f7436326
-- title:
--   Globally Ranked: proposal Count total le
-- statement:
--   The proposal-count sum in Theorem 7.1.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingTotal.lean#L26-L50
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingTotal.lean#L26-L50

import Definitions.Def_TunnellMap_Parking
import Definitions.Def_TunnellMap_ParkingTotal
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalCount_total_le (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M)
    (order : Fin (Fintype.card S) ≃ S) (horder : I.MatchedKeyOrder M order) :
    (∑ s : S, I.proposalCount M s) ≤
      Fintype.card S * (Fintype.card S + 1) / 2 := by sorry
