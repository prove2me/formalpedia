-- Prove2me | Theorems.Thm_SZ_Slice_sq_nonneg
-- name    : SZ.Slice.sq_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:24:06.175283+00:00
-- url     : https://prove2.me/theorems/02e59b01-c1e8-4c73-af34-a42cabdb8c8b
-- title:
--   Slice: sq nonneg
-- statement:
--   The Slice construction uses the sq nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L118-L118
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L118-L118

import Definitions.Def_SZ_Defs
import Definitions.Def_SZ_DigitParity
import Mathlib.Analysis.Real.Sqrt
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Definitions.Def_SZ_Slice
set_option autoImplicit false
open SZ
open Filter Topology
open SZ.Slice
variable (S : Slice)

theorem SZ.Slice.sq_nonneg : 0 ≤ S.sq := by sorry
