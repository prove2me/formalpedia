-- Prove2me | Theorems.Thm_TunnellMap_minusVector_eq_two_vsmul_of_halfDiff
-- name    : TunnellMap.minusVector_eq_two_vsmul_of_halfDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:46.877868+00:00
-- url     : https://prove2.me/theorems/2de7cd26-a8f9-4855-8e27-a46167d89544
-- title:
--   Tunnell Map: minus Vector eq two vsmul of half Diff
-- statement:
--   The Tunnell Map construction uses the minus Vector eq two vsmul of half Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L27-L34
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L27-L34

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_MidpointBound
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.minusVector_eq_two_vsmul_of_halfDiff {n : ℤ}
    (s : BResidual n) (t : AResidual n) (h : Triple)
    (hh : IsHalfDiff h (bLift s.1) (aLift t.1)) :
    minusVector s t = vsmul 2 h := by sorry
