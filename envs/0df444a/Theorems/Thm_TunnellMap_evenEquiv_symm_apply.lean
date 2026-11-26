-- Prove2me | Theorems.Thm_TunnellMap_evenEquiv_symm_apply
-- name    : TunnellMap.evenEquiv_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:05.310282+00:00
-- url     : https://prove2.me/theorems/baccc008-b9a4-5630-9015-3d42f619990c
-- title:
--   Tunnell Map: even Equiv symm apply
-- statement:
--   The Tunnell Map construction uses the even Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Basic.lean#L80-L82
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Basic.lean#L80-L82

import Mathlib
import Definitions.Def_TunnellMap_Basic
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.evenEquiv_symm_apply (n : ℤ) (p : ARep n) :
    (evenEquiv n).symm p = aToEven p := by sorry

attribute [defeq] TunnellMap.evenEquiv_symm_apply
