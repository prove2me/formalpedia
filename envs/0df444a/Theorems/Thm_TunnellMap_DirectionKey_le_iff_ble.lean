-- Prove2me | Theorems.Thm_TunnellMap_DirectionKey_le_iff_ble
-- name    : TunnellMap.DirectionKey.le_iff_ble
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:29:01.150294+00:00
-- url     : https://prove2.me/theorems/23e62ed0-57bb-424c-b81a-b2a32473df12
-- title:
--   Direction Key: le iff ble
-- statement:
--   The Direction Key construction uses the le iff ble property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L120-L121
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L120-L121

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap
open TunnellMap.DirectionKey

theorem TunnellMap.DirectionKey.le_iff_ble (a b : DirectionKey) : a ≤ b ↔ ble a b = true := by sorry
