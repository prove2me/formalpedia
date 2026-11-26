-- Prove2me | Theorems.Thm_TunnellMap_directionKey_eq_iff
-- name    : TunnellMap.directionKey_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:20.156444+00:00
-- url     : https://prove2.me/theorems/8732c6d6-7642-5e3b-b7ce-e39bd044eb84
-- title:
--   Tunnell Map: direction Key eq iff
-- statement:
--   The Tunnell Map construction uses the direction Key eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L146-L155
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L146-L155

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directionKey_eq_iff {v w : Triple} :
    directionKey v = directionKey w ↔ primitiveDirection v = primitiveDirection w := by sorry
