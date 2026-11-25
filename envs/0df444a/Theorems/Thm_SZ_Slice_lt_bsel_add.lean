-- Prove2me | Theorems.Thm_SZ_Slice_lt_bsel_add
-- name    : SZ.Slice.lt_bsel_add
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:17:21.293564+00:00
-- url     : https://prove2.me/theorems/1183e2ae-9b85-47cb-b84e-52f88f9c2e91
-- title:
--   Slice: lt bsel add
-- statement:
--   The Slice construction uses the lt bsel add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L250-L263
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L250-L263

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

theorem SZ.Slice.lt_bsel_add {w : ℝ} (h : S.bsel w < S.e) :
    w < ((S.bsel w : ℝ) + (S.p : ℝ)) * S.sq := by sorry
