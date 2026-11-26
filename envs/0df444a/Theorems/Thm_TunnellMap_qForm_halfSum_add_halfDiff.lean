-- Prove2me | Theorems.Thm_TunnellMap_qForm_halfSum_add_halfDiff
-- name    : TunnellMap.qForm_halfSum_add_halfDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:44.612207+00:00
-- url     : https://prove2.me/theorems/f4237d20-295c-4573-9886-67d84377ab6c
-- title:
--   Tunnell Map: q Form half Sum add half Diff
-- statement:
--   The Tunnell Map construction uses the q Form half Sum add half Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L36-L53
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L36-L53

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_MidpointBound
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.qForm_halfSum_add_halfDiff {n : ℤ}
    (s : BResidual n) (t : AResidual n) (hPlus hMinus : Triple)
    (hPlusEq : IsHalfSum hPlus (bLift s.1) (aLift t.1))
    (hMinusEq : IsHalfDiff hMinus (bLift s.1) (aLift t.1)) :
    qForm hPlus + qForm hMinus = n := by sorry
