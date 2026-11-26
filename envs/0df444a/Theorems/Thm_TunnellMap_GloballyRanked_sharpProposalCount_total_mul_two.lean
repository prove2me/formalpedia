-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_sharpProposalCount_total_mul_two
-- name    : TunnellMap.GloballyRanked.sharpProposalCount_total_mul_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:24.37134+00:00
-- url     : https://prove2.me/theorems/55b4bfe2-a134-4533-9bff-d5f7ae94c6e0
-- title:
--   Globally Ranked: sharp Proposal Count total mul two
-- statement:
--   The Globally Ranked construction uses the sharp Proposal Count total mul two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean#L89-L107
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean#L89-L107

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked

theorem TunnellMap.GloballyRanked.sharpProposalCount_total_mul_two (m : ℕ) :
    (∑ i : Fin m,
      (sharpRanking m).proposalCount (sharpMatching m) i) * 2 =
        m * (m + 1) := by sorry
