-- Prove2me | Theorems.Thm_TunnellMap_square_le_iff_mem_floorCeilInterval
-- name    : TunnellMap.square_le_iff_mem_floorCeilInterval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:49:06.374984+00:00
-- url     : https://prove2.me/theorems/ab0d0887-f993-451c-b996-0279775bd8f3
-- title:
--   Tunnell Map: square le iff mem floor Ceil Interval
-- statement:
--   An integral square lies below `X` exactly when its argument lies between
--   the rational ceiling and floor obtained by dividing by a positive integer.
--   This is the rounding statement used in equation (5.8) of the manuscript.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ShortInterval.lean#L18-L47
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ShortInterval.lean#L18-L47

import Definitions.Def_TunnellMap_AffineLattice
import Mathlib.Data.Int.Order.Lemmas
import Mathlib.Data.Rat.Floor
import Definitions.Def_TunnellMap_ShortInterval
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.square_le_iff_mem_floorCeilInterval {n c X b : ℤ}
    (hn : 0 < n) (hX : 0 ≤ X) :
    (n * b - c) ^ 2 ≤ X ↔
      ⌈((c - Int.sqrt X : ℤ) : ℚ) / (n : ℚ)⌉ ≤ b ∧
        b ≤ ⌊((c + Int.sqrt X : ℤ) : ℚ) / (n : ℚ)⌋ := by sorry
