-- Prove2me | Theorems.Thm_SZ_Slice_one_lt_sq
-- name    : SZ.Slice.one_lt_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:04:34.204093+00:00
-- url     : https://prove2.me/theorems/3ea9e0df-a1c3-4cdb-920d-eacaf6a184d7
-- title:
--   Slice: one lt sq
-- statement:
--   The Slice construction uses the one lt sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L126-L132
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L126-L132

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

theorem SZ.Slice.one_lt_sq : 1 < S.sq := by sorry
