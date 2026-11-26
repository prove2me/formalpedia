-- Prove2me | Theorems.Thm_TunnellMap_Examples41_edgeKey_s4_t1
-- name    : TunnellMap.Examples41.edgeKey_s4_t1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:28:28.064516+00:00
-- url     : https://prove2.me/theorems/cb720b5b-0756-5f11-ba35-4a8c140b5e82
-- title:
--   Examples41: edge Key s4 t1
-- statement:
--   The Examples41 construction uses the edge Key s4 t1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L363-L370
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L363-L370

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.edgeKey_s4_t1 : representativeEdgeKey s4 t1 = key41 20 1 4 1 := by sorry
