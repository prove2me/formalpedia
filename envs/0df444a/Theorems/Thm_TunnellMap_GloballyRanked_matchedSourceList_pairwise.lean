-- Prove2me | Theorems.Thm_TunnellMap_GloballyRanked_matchedSourceList_pairwise
-- name    : TunnellMap.GloballyRanked.matchedSourceList_pairwise
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:01:44.844572+00:00
-- url     : https://prove2.me/theorems/68107751-f5a5-4e1a-82db-ee9925260eea
-- title:
--   Globally Ranked: matched Source List pairwise
-- statement:
--   The Globally Ranked construction uses the matched Source List pairwise property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MatchedOrder.lean#L25-L34
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MatchedOrder.lean#L25-L34

import Definitions.Def_TunnellMap_ParkingTotal
import Mathlib.Data.List.NodupEquivFin
import Definitions.Def_TunnellMap_MatchedOrder
set_option autoImplicit true
open TunnellMap
open TunnellMap.GloballyRanked
variable {K S T : Type*} [LinearOrder K] [Fintype S] [Fintype T]
  [DecidableEq S] [DecidableEq T]

theorem TunnellMap.GloballyRanked.matchedSourceList_pairwise (I : GloballyRanked K S T) (M : S ≃ T) :
    (I.matchedSourceList M).Pairwise fun s₁ s₂ =>
      I.rank s₁ (M s₁) ≤ I.rank s₂ (M s₂) := by sorry
