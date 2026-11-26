-- Prove2me | Theorems.Thm_TunnellMap_plus_minus_orthogonal
-- name    : TunnellMap.plus_minus_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:26.342884+00:00
-- url     : https://prove2.me/theorems/bdb665f5-779e-5e26-9b4b-2c966ea84522
-- title:
--   Tunnell Map: plus minus orthogonal
-- statement:
--   The Tunnell Map construction uses the plus minus orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L187-L193
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L187-L193

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.plus_minus_orthogonal {n : ℤ} (s : BResidual n) (t : AResidual n) :
    qBilinear (plusVector s t) (minusVector s t) = 0 := by sorry
