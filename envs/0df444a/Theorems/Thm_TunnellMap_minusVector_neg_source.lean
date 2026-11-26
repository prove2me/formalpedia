-- Prove2me | Theorems.Thm_TunnellMap_minusVector_neg_source
-- name    : TunnellMap.minusVector_neg_source
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:21:01.033124+00:00
-- url     : https://prove2.me/theorems/8308c146-8dd2-571d-a830-a52073a678d7
-- title:
--   Tunnell Map: minus Vector neg source
-- statement:
--   The Tunnell Map construction uses the minus Vector neg source property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L263-L266
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L263-L266

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.minusVector_neg_source {n : ℤ} (s : BResidual n) (t : AResidual n) :
    minusVector (negBResidual s) t = negTriple (plusVector s t) := by sorry
