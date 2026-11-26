-- Prove2me | Theorems.Thm_TunnellMap_halfDiff_is_halfSum_neg
-- name    : TunnellMap.halfDiff_is_halfSum_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:46:35.00658+00:00
-- url     : https://prove2.me/theorems/d6eb5ee1-73a5-53ea-a37a-b479229d2429
-- title:
--   Tunnell Map: half Diff is half Sum neg
-- statement:
--   The Tunnell Map construction uses the half Diff is half Sum neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointRecord.lean#L19-L24
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointRecord.lean#L19-L24

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_MidpointBound
import Definitions.Def_TunnellMap_MidpointRecord
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.halfDiff_is_halfSum_neg {h E F : Triple}
    (hh : IsHalfDiff h E F) : IsHalfSum h E (negTriple F) := by sorry
