-- Prove2me | Theorems.Thm_TunnellMap_assemble_inr
-- name    : TunnellMap.assemble_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:40:39.894893+00:00
-- url     : https://prove2.me/theorems/64e00a47-e134-4034-afc7-6a28f38ed64b
-- title:
--   Tunnell Map: assemble inr
-- statement:
--   The Tunnell Map construction uses the assemble inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L25-L27
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L25-L27

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}

theorem TunnellMap.assemble_inr (even : E ≃ A) (odd : O ≃ A) (o : O) :
    assemble even odd (Sum.inr o) = odd o := by sorry

attribute [defeq] TunnellMap.assemble_inr
