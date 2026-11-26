-- Prove2me | Theorems.Thm_TunnellMap_DirectionKey_lt_iff
-- name    : TunnellMap.DirectionKey.lt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:41.805326+00:00
-- url     : https://prove2.me/theorems/c28eebb0-1d6c-51c6-9411-33091b163118
-- title:
--   Direction Key: lt iff
-- statement:
--   The order on keys is the lexicographic order of the four components.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L124-L128
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L124-L128

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap
open TunnellMap.DirectionKey

theorem TunnellMap.DirectionKey.lt_iff (a b : DirectionKey) :
    a < b ↔ a.form < b.form ∨ (a.form = b.form ∧ (a.x < b.x ∨ (a.x = b.x ∧
      (a.y < b.y ∨ (a.y = b.y ∧ a.z < b.z))))) := by sorry
