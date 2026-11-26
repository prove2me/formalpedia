-- Prove2me | Theorems.Thm_TunnellMap_Examples41_edgeKey_s2_t1
-- name    : TunnellMap.Examples41.edgeKey_s2_t1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:26:25.466469+00:00
-- url     : https://prove2.me/theorems/38b0582a-1b94-400b-88ac-92d43edabb0d
-- title:
--   Examples41: edge Key s2 t1
-- statement:
--   The Examples41 construction uses the edge Key s2 t1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L291-L298
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L291-L298

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.edgeKey_s2_t1 : representativeEdgeKey s2 t1 = key41 5 1 (-1) 1 := by sorry
