-- Prove2me | Theorems.Thm_TunnellMap_Examples41_edgeKey_s1_t3
-- name    : TunnellMap.Examples41.edgeKey_s1_t3
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:28:55.674426+00:00
-- url     : https://prove2.me/theorems/a60e0795-c3b0-45f8-a1e4-17cad7c0db0d
-- title:
--   Examples41: edge Key s1 t3
-- statement:
--   The Examples41 construction uses the edge Key s1 t3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L273-L280
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L273-L280

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.edgeKey_s1_t3 : representativeEdgeKey s1 t3 = key41 5 1 1 (-1) := by sorry
