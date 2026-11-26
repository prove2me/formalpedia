-- Prove2me | Theorems.Thm_TunnellMap_plus_minus_directions_ne
-- name    : TunnellMap.plus_minus_directions_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:30.75896+00:00
-- url     : https://prove2.me/theorems/25f8af00-1931-5eb6-a912-2cfbfd075a9a
-- title:
--   Tunnell Map: plus minus directions ne
-- statement:
--   The two signed midpoint lines have distinct primitive directions.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L196-L213
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L196-L213

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.plus_minus_directions_ne {n : ℤ} (s : BResidual n) (t : AResidual n) :
    primitiveDirection (plusVector s t) ≠ primitiveDirection (minusVector s t) := by sorry
