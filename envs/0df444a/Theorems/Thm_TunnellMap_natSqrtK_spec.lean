-- Prove2me | Theorems.Thm_TunnellMap_natSqrtK_spec
-- name    : TunnellMap.natSqrtK_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:36:29.933679+00:00
-- url     : https://prove2.me/theorems/702c8cf7-5ed5-438e-8795-14d9095238d3
-- title:
--   Tunnell Map: nat Sqrt K spec
-- statement:
--   The Tunnell Map construction uses the nat Sqrt K spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L75-L78
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/KernelArith.lean#L75-L78

import Mathlib
import Definitions.Def_TunnellMap_KernelArith
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.natSqrtK_spec (n : ℕ) :
    natSqrtK n * natSqrtK n ≤ n ∧ n < (natSqrtK n + 1) * (natSqrtK n + 1) := by sorry
