-- Prove2me | Theorems.Thm_P2M_SZ_Slice_U_def__de67dd39ecba
-- name    : P2M_SZ_Slice_U_def__de67dd39ecba
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:15:13.736737+00:00
-- url     : https://prove2.me/theorems/29eeb3dd-f5b2-47f9-9f78-84a276be8100
-- title:
--   P2 M SZ Slice U def  de67dd39ecba: P2 M SZ Slice U def  de67dd39ecba
-- statement:
--   The window equation, phrased with `S.sq`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L121-L121
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L121-L121

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

theorem P2M_SZ_Slice_U_def__de67dd39ecba : ((S.m : ℝ) - 1) * S.U = (S.e : ℝ) * (1 + S.sq) := by sorry

alias «SZ».«Slice».«U_def'» := P2M_SZ_Slice_U_def__de67dd39ecba
