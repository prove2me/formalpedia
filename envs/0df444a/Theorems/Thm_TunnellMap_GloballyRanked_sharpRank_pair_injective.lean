-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_sharpRank_pair_injective
-- name    : TunnellMap.GloballyRanked.sharpRank_pair_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:19:53.630612+00:00
-- url     : https://prove2.me/theorems/1eda313e-34e9-5b46-a042-45d52deabffb
-- title:
--   Globally Ranked: sharp Rank pair injective
-- statement:
--   Every edge of the sharpness instance has a different global key.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean#L40-L56
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Sharpness.lean#L40-L56

import Definitions.Def_TunnellMap_ParkingRearrangement
import Definitions.Def_TunnellMap_Sharpness
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked

theorem TunnellMap.GloballyRanked.sharpRank_pair_injective (m : ℕ) :
    Function.Injective (fun e : Fin m × Fin m =>
      (sharpRanking m).rank e.1 e.2) := by sorry
