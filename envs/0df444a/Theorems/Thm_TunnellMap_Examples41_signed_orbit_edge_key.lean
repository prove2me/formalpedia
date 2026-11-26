-- Prove2me | Theorems.Thm_TunnellMap_Examples41_signed_orbit_edge_key
-- name    : TunnellMap.Examples41.signed_orbit_edge_key
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:25:12.013194+00:00
-- url     : https://prove2.me/theorems/2f58e379-691c-4b54-9191-58c23d18409e
-- title:
--   Examples41: signed orbit edge key
-- statement:
--   The Examples41 construction uses the signed orbit edge key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L239-L248
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L239-L248

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.signed_orbit_edge_key :
    representativeEdgeKey s1 t1 = (⟨5, 1, -1, -1⟩ : DirectionKey) := by sorry
