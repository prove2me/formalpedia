-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_sharpProposalCount
-- name    : TunnellMap.GloballyRanked.sharpProposalCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:34:12.873054+00:00
-- url     : https://prove2.me/theorems/e3c76748-6efa-5b8b-893f-9365a0323135
-- title:
--   Globally Ranked: sharp Proposal Count
-- statement:
--   Source `i` has exactly `i + 1` proposals in zero-based notation.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean#L76-L87
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean#L76-L87

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked

theorem TunnellMap.GloballyRanked.sharpProposalCount (m : ℕ) (i : Fin m) :
    (sharpRanking m).proposalCount (sharpMatching m) i = i.1 + 1 := by sorry
