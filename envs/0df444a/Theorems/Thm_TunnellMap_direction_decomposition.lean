-- Prove2me | Theorems.Thm_TunnellMap_direction_decomposition
-- name    : TunnellMap.direction_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:13.554214+00:00
-- url     : https://prove2.me/theorems/e31a68b1-f38f-5875-8ecf-2d3080eeb997
-- title:
--   Tunnell Map: direction decomposition
-- statement:
--   Every integer vector is an integral multiple of the paper-oriented
--   primitive part selected from its line.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L310-L320
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L310-L320

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.direction_decomposition (v : Triple) :
    v = vsmul (directionScale v) (primitiveDirection v) := by sorry
