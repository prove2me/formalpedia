-- Prove2me | Theorems.Thm_TunnellMap_Examples41_edgeKey_s3_t1
-- name    : TunnellMap.Examples41.edgeKey_s3_t1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:28:57.118704+00:00
-- url     : https://prove2.me/theorems/00f6ed5f-efb7-4e0f-afc7-099c207da430
-- title:
--   Examples41: edge Key s3 t1
-- statement:
--   The Examples41 construction uses the edge Key s3 t1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L327-L334
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L327-L334

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.edgeKey_s3_t1 : representativeEdgeKey s3 t1 = key41 20 1 4 (-1) := by sorry
