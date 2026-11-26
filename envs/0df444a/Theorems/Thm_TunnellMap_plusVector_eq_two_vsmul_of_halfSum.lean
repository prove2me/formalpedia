-- Prove2me | Theorems.Thm_TunnellMap_plusVector_eq_two_vsmul_of_halfSum
-- name    : TunnellMap.plusVector_eq_two_vsmul_of_halfSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:23:37.693193+00:00
-- url     : https://prove2.me/theorems/6db66508-33f7-5ae1-a3cb-d94c44687728
-- title:
--   Tunnell Map: plus Vector eq two vsmul of half Sum
-- statement:
--   The Tunnell Map construction uses the plus Vector eq two vsmul of half Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L18-L25
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/MidpointBound.lean#L18-L25

import Definitions.Def_TunnellMap_ProjectiveKey
import Definitions.Def_TunnellMap_MidpointBound
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.plusVector_eq_two_vsmul_of_halfSum {n : ℤ}
    (s : BResidual n) (t : AResidual n) (h : Triple)
    (hh : IsHalfSum h (bLift s.1) (aLift t.1)) :
    plusVector s t = vsmul 2 h := by sorry
