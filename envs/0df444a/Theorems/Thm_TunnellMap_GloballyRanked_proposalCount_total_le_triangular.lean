-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_proposalCount_total_le_triangular
-- name    : TunnellMap.GloballyRanked.proposalCount_total_le_triangular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:01:24.662175+00:00
-- url     : https://prove2.me/theorems/dfa975ce-2df9-59c3-8265-0e61935f0948
-- title:
--   Globally Ranked: proposal Count total le triangular
-- statement:
--   The parameter-free triangular proposal bound of Theorem 7.1.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MatchedOrder.lean#L84-L89
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MatchedOrder.lean#L84-L89

import Definitions.Def_TunnellMap_ParkingTotal
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_TunnellMap_MatchedOrder
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.proposalCount_total_le_triangular (I : GloballyRanked K S T)
    (M : S ≃ T) (hM : I.Stable M) :
    (∑ s : S, I.proposalCount M s) ≤
      Fintype.card S * (Fintype.card S + 1) / 2 := by sorry
