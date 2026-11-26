-- Prove2me | Theorems.Thm_TunnellMap_Examples41_sharpness_three_sources
-- name    : TunnellMap.Examples41.sharpness_three_sources
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:24:07.081779+00:00
-- url     : https://prove2.me/theorems/76b62784-a85f-4113-ab2f-c6260ff7c923
-- title:
--   Examples41: sharpness three sources
-- statement:
--   The Examples41 construction uses the sharpness three sources property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L207-L218
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L207-L218

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.sharpness_three_sources :
    (sharpRanking 3).proposalCount (sharpMatching 3) (0 : Fin 3) = 1 ∧
      (sharpRanking 3).proposalCount (sharpMatching 3) (1 : Fin 3) = 2 ∧
      (sharpRanking 3).proposalCount (sharpMatching 3) (2 : Fin 3) = 3 ∧
      (∑ i : Fin 3, (sharpRanking 3).proposalCount (sharpMatching 3) i) = 6 := by sorry
