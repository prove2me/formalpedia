-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalCounts_isParkingFunction
-- name    : TunnellMap.GloballyRanked.proposalCounts_isParkingFunction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:19:56.97481+00:00
-- url     : https://prove2.me/theorems/10ef4788-86b2-5539-8ddf-588f024fc298
-- title:
--   Globally Ranked: proposal Counts is Parking Function
-- statement:
--   The literal sorted-rearrangement statement of Theorem 7.1.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingRearrangement.lean#L112-L128
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingRearrangement.lean#L112-L128

import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_ParkingRearrangement
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalCounts_isParkingFunction (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) :
    IsParkingFunction (I.matchedProposalCounts M) := by sorry
