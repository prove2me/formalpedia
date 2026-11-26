-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_sharpProposalCount_total
-- name    : TunnellMap.GloballyRanked.sharpProposalCount_total
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:46:04.380103+00:00
-- url     : https://prove2.me/theorems/713b2011-28fc-4f92-a6cb-8707b3bcd6a1
-- title:
--   Globally Ranked: sharp Proposal Count total
-- statement:
--   Proposition 7.2: the triangular bound is attained for every size.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean#L110-L115
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean#L110-L115

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked

theorem TunnellMap.GloballyRanked.sharpProposalCount_total (m : ℕ) :
    (∑ i : Fin m,
      (sharpRanking m).proposalCount (sharpMatching m) i) =
        m * (m + 1) / 2 := by sorry
