-- Prove2me | Theorems.Thm_P2M_SZ_Slice_gap__61b112f6735f
-- name    : P2M_SZ_Slice_gap__61b112f6735f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:42:05.379814+00:00
-- url     : https://prove2.me/theorems/1e2e616e-1e10-4651-83a3-ac06f1312964
-- title:
--   P2 M SZ Slice gap  61b112f6735f: P2 M SZ Slice gap  61b112f6735f
-- statement:
--   The second gap condition, phrased with `S.sq`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L124-L124
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L124-L124

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

theorem P2M_SZ_Slice_gap__61b112f6735f : (S.p : ℝ) * S.sq - (S.e : ℝ) ≤ S.U := by sorry

alias «SZ».«Slice».«gap'» := P2M_SZ_Slice_gap__61b112f6735f
