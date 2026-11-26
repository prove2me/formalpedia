-- Prove2me | Theorems.Thm_TunnellMap_natSqrtK_eq
-- name    : TunnellMap.natSqrtK_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:40.958797+00:00
-- url     : https://prove2.me/theorems/c141d64d-a4a5-5447-b4b9-cf9fa296f7e6
-- title:
--   Tunnell Map: nat Sqrt K eq
-- statement:
--   The binary-search square root is `Nat.sqrt`.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L81-L85
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L81-L85

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.natSqrtK_eq (n : ℕ) : natSqrtK n = Nat.sqrt n := by sorry
