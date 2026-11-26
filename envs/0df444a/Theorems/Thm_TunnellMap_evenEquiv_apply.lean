-- Prove2me | Theorems.Thm_TunnellMap_evenEquiv_apply
-- name    : TunnellMap.evenEquiv_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:37:09.517402+00:00
-- url     : https://prove2.me/theorems/9a899ba9-5fe7-4dbb-94a6-00707ce0b1c3
-- title:
--   Tunnell Map: even Equiv apply
-- statement:
--   The Tunnell Map construction uses the even Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Basic.lean#L76-L78
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Basic.lean#L76-L78

import Mathlib
import Definitions.Def_TunnellMap_Basic
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.evenEquiv_apply (n : ℤ) (p : BEvenParam n) :
    (evenEquiv n p).1 = ⟨p.x, p.y, p.w⟩ := by sorry

attribute [defeq] TunnellMap.evenEquiv_apply
