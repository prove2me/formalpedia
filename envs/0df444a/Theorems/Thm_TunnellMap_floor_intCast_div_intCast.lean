-- Prove2me | Theorems.Thm_TunnellMap_floor_intCast_div_intCast
-- name    : TunnellMap.floor_intCast_div_intCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:48.240563+00:00
-- url     : https://prove2.me/theorems/c5764806-a873-5ae2-a535-66ca5b7af211
-- title:
--   Tunnell Map: floor int Cast div int Cast
-- statement:
--   The Tunnell Map construction uses the floor int Cast div int Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L95-L97
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L95-L97

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.floor_intCast_div_intCast (a b : ℤ) (hb : 0 ≤ b) :
    ⌊((a : ℚ) / (b : ℚ))⌋ = a / b := by sorry
