-- Prove2me | Theorems.Thm_TunnellMap_directionKey_primitiveDirection
-- name    : TunnellMap.directionKey_primitiveDirection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:20:59.150911+00:00
-- url     : https://prove2.me/theorems/9c346f73-25c6-58de-a897-f60352ae9ca8
-- title:
--   Tunnell Map: direction Key primitive Direction
-- statement:
--   The Tunnell Map construction uses the direction Key primitive Direction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L244-L248
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L244-L248

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directionKey_primitiveDirection {v : Triple}
    (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKey (primitiveDirection v) = directionKey v := by sorry
