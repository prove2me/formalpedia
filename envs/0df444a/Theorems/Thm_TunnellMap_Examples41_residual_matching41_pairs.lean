-- Prove2me | Theorems.Thm_TunnellMap_Examples41_residual_matching41_pairs
-- name    : TunnellMap.Examples41.residual_matching41_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:21:30.318793+00:00
-- url     : https://prove2.me/theorems/c1124dbb-0974-5c8d-b06d-6ee5400323cb
-- title:
--   Examples41: residual matching41 pairs
-- statement:
--   The Examples41 construction uses the residual matching41 pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L116-L119
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L116-L119

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.residual_matching41_pairs :
    residualMatching41 0 = 0 ∧ residualMatching41 1 = 1 ∧
      residualMatching41 2 = 3 ∧ residualMatching41 3 = 2 := by sorry
