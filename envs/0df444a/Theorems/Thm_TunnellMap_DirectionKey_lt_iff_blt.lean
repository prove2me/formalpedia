-- Prove2me | Theorems.Thm_TunnellMap_DirectionKey_lt_iff_blt
-- name    : TunnellMap.DirectionKey.lt_iff_blt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:00.495189+00:00
-- url     : https://prove2.me/theorems/fee065bd-d94d-53cf-9391-9c96e0c81e29
-- title:
--   Direction Key: lt iff blt
-- statement:
--   The Direction Key construction uses the lt iff blt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L117-L118
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L117-L118

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap
open TunnellMap.DirectionKey

theorem TunnellMap.DirectionKey.lt_iff_blt (a b : DirectionKey) : a < b ↔ blt a b = true := by sorry
