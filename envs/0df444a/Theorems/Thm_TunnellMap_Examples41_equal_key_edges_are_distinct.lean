-- Prove2me | Theorems.Thm_TunnellMap_Examples41_equal_key_edges_are_distinct
-- name    : TunnellMap.Examples41.equal_key_edges_are_distinct
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T17:06:42.217186+00:00
-- url     : https://prove2.me/theorems/c18cb2cd-81f3-5cf3-bc9e-de5299463bab
-- title:
--   Examples41: equal key edges are distinct
-- statement:
--   The Examples41 construction uses the equal key edges are distinct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L421-L431
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L421-L431

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.equal_key_edges_are_distinct :
    representativeEdgeKey s1 t1 = representativeEdgeKey s3 t4 ∧
      s1 ≠ s3 ∧ t1 ≠ t4 := by sorry
