-- Prove2me | Theorems.Thm_TunnellMap_Examples41_signed_orbit_edge_prefers_negative_target
-- name    : TunnellMap.Examples41.signed_orbit_edge_prefers_negative_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:43:34.990753+00:00
-- url     : https://prove2.me/theorems/a94687db-d3fe-55bf-ab5f-ace37a44bbf9
-- title:
--   Examples41: signed orbit edge prefers negative target
-- statement:
--   The Examples41 construction uses the signed orbit edge prefers negative target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L250-L260
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Residual.lean#L250-L260

import Definitions.Def_TunnellMap_Examples41
import Definitions.Def_TunnellMap_Examples41Residual
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.signed_orbit_edge_prefers_negative_target :
    preferredTarget s1 t1 = negAResidual t1 := by sorry
