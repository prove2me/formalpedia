-- Prove2me | Theorems.Thm_TunnellMap_Examples41_edgeKey_s3_t3
-- name    : TunnellMap.Examples41.edgeKey_s3_t3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:28:18.98822+00:00
-- url     : https://prove2.me/theorems/a800f511-7f15-450b-9c1d-0b4d76b7cd51
-- title:
--   Examples41: edge Key s3 t3
-- statement:
--   The Examples41 construction uses the edge Key s3 t3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L345-L352
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L345-L352

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.edgeKey_s3_t3 : representativeEdgeKey s3 t3 = key41 20 1 (-4) (-1) := by sorry
