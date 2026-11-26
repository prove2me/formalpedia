-- Prove2me | Theorems.Thm_TunnellMap_plusVector_neg_source
-- name    : TunnellMap.plusVector_neg_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:06.324885+00:00
-- url     : https://prove2.me/theorems/8fa5f69d-2859-5113-97c7-812f9e9a8c12
-- title:
--   Tunnell Map: plus Vector neg source
-- statement:
--   The Tunnell Map construction uses the plus Vector neg source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L258-L261
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L258-L261

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.plusVector_neg_source {n : ℤ} (s : BResidual n) (t : AResidual n) :
    plusVector (negBResidual s) t = negTriple (minusVector s t) := by sorry
