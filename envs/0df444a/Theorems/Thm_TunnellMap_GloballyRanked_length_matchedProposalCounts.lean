-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_length_matchedProposalCounts
-- name    : TunnellMap.GloballyRanked.length_matchedProposalCounts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:29:27.055592+00:00
-- url     : https://prove2.me/theorems/84068a2e-4c03-41be-9504-2d441f3fc770
-- title:
--   Globally Ranked: length matched Proposal Counts
-- statement:
--   The Globally Ranked construction uses the length matched Proposal Counts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingRearrangement.lean#L106-L109
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ParkingRearrangement.lean#L106-L109

import Definitions.Def_TunnellMap_MatchedOrder
import Definitions.Def_TunnellMap_ParkingRearrangement
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.length_matchedProposalCounts
    (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedProposalCounts M).length = Fintype.card S := by sorry
