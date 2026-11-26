-- Prove2me | Theorems.Thm_TunnellMap_directionKey_negTriple
-- name    : TunnellMap.directionKey_negTriple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:55.602495+00:00
-- url     : https://prove2.me/theorems/f0dd2287-6c58-442c-beb0-0e4c87a1741d
-- title:
--   Tunnell Map: direction Key neg Triple
-- statement:
--   The Tunnell Map construction uses the direction Key neg Triple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L157-L159
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L157-L159

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.directionKey_negTriple {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    directionKey (negTriple v) = directionKey v := by sorry
