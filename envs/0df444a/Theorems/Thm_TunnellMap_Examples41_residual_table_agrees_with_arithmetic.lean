-- Prove2me | Theorems.Thm_TunnellMap_Examples41_residual_table_agrees_with_arithmetic
-- name    : TunnellMap.Examples41.residual_table_agrees_with_arithmetic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:22:13.125259+00:00
-- url     : https://prove2.me/theorems/4e6c88ff-0cb8-49e9-bea8-78f16675064b
-- title:
--   Examples41: residual table agrees with arithmetic
-- statement:
--   The Examples41 construction uses the residual table agrees with arithmetic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L67-L88
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L67-L88

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.residual_table_agrees_with_arithmetic :
    residualRanking41.rank 0 0 = representativeEdgeKey s1 t1 ∧
      residualRanking41.rank 0 1 = representativeEdgeKey s1 t2 ∧
      residualRanking41.rank 0 2 = representativeEdgeKey s1 t3 ∧
      residualRanking41.rank 0 3 = representativeEdgeKey s1 t4 ∧
      residualRanking41.rank 1 0 = representativeEdgeKey s2 t1 ∧
      residualRanking41.rank 1 1 = representativeEdgeKey s2 t2 ∧
      residualRanking41.rank 1 2 = representativeEdgeKey s2 t3 ∧
      residualRanking41.rank 1 3 = representativeEdgeKey s2 t4 ∧
      residualRanking41.rank 2 0 = representativeEdgeKey s3 t1 ∧
      residualRanking41.rank 2 1 = representativeEdgeKey s3 t2 ∧
      residualRanking41.rank 2 2 = representativeEdgeKey s3 t3 ∧
      residualRanking41.rank 2 3 = representativeEdgeKey s3 t4 ∧
      residualRanking41.rank 3 0 = representativeEdgeKey s4 t1 ∧
      residualRanking41.rank 3 1 = representativeEdgeKey s4 t2 ∧
      residualRanking41.rank 3 2 = representativeEdgeKey s4 t3 ∧
      residualRanking41.rank 3 3 = representativeEdgeKey s4 t4 := by sorry
