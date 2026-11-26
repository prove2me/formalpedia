-- Prove2me | Theorems.Thm_TunnellMap_minusVector_neg_target
-- name    : TunnellMap.minusVector_neg_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:17.489826+00:00
-- url     : https://prove2.me/theorems/9ca12226-3503-41be-b0b2-cfee025cda0a
-- title:
--   Tunnell Map: minus Vector neg target
-- statement:
--   The Tunnell Map construction uses the minus Vector neg target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L273-L276
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L273-L276

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.minusVector_neg_target {n : ℤ} (s : BResidual n) (t : AResidual n) :
    minusVector s (negAResidual t) = plusVector s t := by sorry
