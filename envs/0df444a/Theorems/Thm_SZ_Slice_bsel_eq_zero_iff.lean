-- Prove2me | Theorems.Thm_SZ_Slice_bsel_eq_zero_iff
-- name    : SZ.Slice.bsel_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:51:45.682868+00:00
-- url     : https://prove2.me/theorems/e2e90538-bb2b-58c5-9ef1-d1428ddacdf9
-- title:
--   Slice: bsel eq zero iff
-- statement:
--   `b = 0` exactly on `L = [0, p√m)` — the paper's (5.2), immediate from the formula.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L266-L286
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L266-L286

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

theorem SZ.Slice.bsel_eq_zero_iff {w : ℝ} (h0 : 0 ≤ w) : S.bsel w = 0 ↔ w < (S.p : ℝ) * S.sq := by sorry
