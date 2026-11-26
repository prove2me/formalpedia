-- Prove2me | Theorems.Thm_TunnellMap_Examples41_edgeKey_s3_t4
-- name    : TunnellMap.Examples41.edgeKey_s3_t4
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:24:41.316943+00:00
-- url     : https://prove2.me/theorems/d0b35396-d45b-4972-a2ea-16ee0deb9777
-- title:
--   Examples41: edge Key s3 t4
-- statement:
--   The Examples41 construction uses the edge Key s3 t4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L354-L361
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L354-L361

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.edgeKey_s3_t4 : representativeEdgeKey s3 t4 = key41 5 1 (-1) (-1) := by sorry
