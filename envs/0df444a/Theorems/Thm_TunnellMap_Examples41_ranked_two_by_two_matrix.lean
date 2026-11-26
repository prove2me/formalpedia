-- Prove2me | Theorems.Thm_TunnellMap_Examples41_ranked_two_by_two_matrix
-- name    : TunnellMap.Examples41.ranked_two_by_two_matrix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:20:39.633179+00:00
-- url     : https://prove2.me/theorems/8be8372a-b9e3-54c1-bd94-815cf950729c
-- title:
--   Examples41: ranked two by two matrix
-- statement:
--   The Examples41 construction uses the ranked two by two matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L31-L34
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L31-L34

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.ranked_two_by_two_matrix :
    ranking2.rank 0 0 = 1 ∧ ranking2.rank 0 1 = 3 ∧
      ranking2.rank 1 0 = 2 ∧ ranking2.rank 1 1 = 4 := by sorry
