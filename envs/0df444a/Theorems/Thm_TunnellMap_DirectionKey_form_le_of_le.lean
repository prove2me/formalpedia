-- Prove2me | Theorems.Thm_TunnellMap_DirectionKey_form_le_of_le
-- name    : TunnellMap.DirectionKey.form_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:52.755842+00:00
-- url     : https://prove2.me/theorems/10c2f08b-9898-4df5-9e15-b67a10e64948
-- title:
--   Direction Key: form le of le
-- statement:
--   The first component of a key is monotone.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L131-L138
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L131-L138

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap
open TunnellMap.DirectionKey

theorem TunnellMap.DirectionKey.form_le_of_le {a b : DirectionKey} (h : a ≤ b) : a.form ≤ b.form := by sorry
