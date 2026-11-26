-- Prove2me | Theorems.Thm_TunnellMap_assemble_inl
-- name    : TunnellMap.assemble_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:30.001184+00:00
-- url     : https://prove2.me/theorems/77ccd4c5-37df-5c83-88ab-b1fcdb45d63c
-- title:
--   Tunnell Map: assemble inl
-- statement:
--   The Tunnell Map construction uses the assemble inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L21-L23
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L21-L23

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}

theorem TunnellMap.assemble_inl (even : E ≃ A) (odd : O ≃ A) (e : E) :
    assemble even odd (Sum.inl e) = even e := by sorry

attribute [defeq] TunnellMap.assemble_inl
