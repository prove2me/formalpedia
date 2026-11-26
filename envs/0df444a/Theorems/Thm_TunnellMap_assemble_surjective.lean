-- Prove2me | Theorems.Thm_TunnellMap_assemble_surjective
-- name    : TunnellMap.assemble_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:34.943686+00:00
-- url     : https://prove2.me/theorems/2eb4a49f-65ef-48da-9af5-492a24af46df
-- title:
--   Tunnell Map: assemble surjective
-- statement:
--   The Tunnell Map construction uses the assemble surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L29-L32
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Assembly.lean#L29-L32

import Definitions.Def_TunnellMap_Basic
import Definitions.Def_TunnellMap_Assembly
set_option autoImplicit true
open TunnellMap
variable {E O A : Type*}

theorem TunnellMap.assemble_surjective (even : E ≃ A) (odd : O ≃ A) :
    Function.Surjective (assemble even odd) := by sorry
