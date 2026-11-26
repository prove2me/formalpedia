-- Prove2me | Theorems.Thm_TunnellMap_ceil_intCast_div_intCast
-- name    : TunnellMap.ceil_intCast_div_intCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:34.579235+00:00
-- url     : https://prove2.me/theorems/190930ca-2b1b-54ad-80fd-9ce939df41c4
-- title:
--   Tunnell Map: ceil int Cast div int Cast
-- statement:
--   The Tunnell Map construction uses the ceil int Cast div int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L99-L102
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L99-L102

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.ceil_intCast_div_intCast (a b : ℤ) (hb : 0 ≤ b) :
    ⌈((a : ℚ) / (b : ℚ))⌉ = -((-a) / b) := by sorry
