-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_le_position
-- name    : TunnellMap.GloballyRanked.proposalCount_le_position
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:04.733175+00:00
-- url     : https://prove2.me/theorems/2ab42434-2a7c-56dd-af50-cc23f424f32e
-- title:
--   Globally Ranked: proposal Count le position
-- statement:
--   The indexed form of Theorem 7.1, with zero-based indices.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean#L99-L105
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Parking.lean#L99-L105

import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_Parking
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]
omit [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalCount_le_position (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M)
    (order : Fin (Fintype.card S) ≃ S) (horder : I.MatchedKeyOrder M order)
    (i : Fin (Fintype.card S)) :
    I.proposalCount M (order i) ≤ i.1 + 1 := by sorry
