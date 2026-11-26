-- Prove2me | Theorems.Thm_TunnellMap_Examples41_ranked_two_by_two_proposal_logic
-- name    : TunnellMap.Examples41.ranked_two_by_two_proposal_logic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:20:46.731344+00:00
-- url     : https://prove2.me/theorems/3968c7cd-bb3b-5fde-85b1-6f16317e3d05
-- title:
--   Examples41: ranked two by two proposal logic
-- statement:
--   The Examples41 construction uses the ranked two by two proposal logic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L41-L45
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L41-L45

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.ranked_two_by_two_proposal_logic :
    ranking2.rank 0 0 < ranking2.rank 0 1 ∧
      ranking2.rank 1 0 < ranking2.rank 1 1 ∧
      ranking2.rank 0 0 < ranking2.rank 1 0 := by sorry
