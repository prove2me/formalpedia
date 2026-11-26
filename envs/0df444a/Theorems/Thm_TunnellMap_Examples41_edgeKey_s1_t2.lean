-- Prove2me | Theorems.Thm_TunnellMap_Examples41_edgeKey_s1_t2
-- name    : TunnellMap.Examples41.edgeKey_s1_t2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:27:43.069946+00:00
-- url     : https://prove2.me/theorems/66983dab-0f79-4549-b3c2-7e92ed9610e2
-- title:
--   Examples41: edge Key s1 t2
-- statement:
--   The Examples41 construction uses the edge Key s1 t2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L264-L271
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L264-L271

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.edgeKey_s1_t2 : representativeEdgeKey s1 t2 = key41 20 1 (-4) (-1) := by sorry
