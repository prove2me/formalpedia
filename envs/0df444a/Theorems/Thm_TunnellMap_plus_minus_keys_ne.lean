-- Prove2me | Theorems.Thm_TunnellMap_plus_minus_keys_ne
-- name    : TunnellMap.plus_minus_keys_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:37.392533+00:00
-- url     : https://prove2.me/theorems/b734eb50-19d1-480e-9f8e-ca0a9d7ad031
-- title:
--   Tunnell Map: plus minus keys ne
-- statement:
--   The Tunnell Map construction uses the plus minus keys ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L215-L218
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L215-L218

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.plus_minus_keys_ne {n : ℤ} (s : BResidual n) (t : AResidual n) :
    directionKey (plusVector s t) ≠ directionKey (minusVector s t) := by sorry
