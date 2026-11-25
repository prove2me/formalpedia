-- Prove2me | Theorems.Thm_SZ_Slice_pick_adm
-- name    : SZ.Slice.pick_adm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:07:09.061507+00:00
-- url     : https://prove2.me/theorems/1eed7844-8ca5-449a-8a83-f8cbde5c7e31
-- title:
--   Slice: pick adm
-- statement:
--   **The cover lemma.**  At every `w ∈ [0, mU]` the selected offset is admissible: both
--   digits lie in `Ev` and the residual `w - a - b√m` lies in `[0, U]`.  This is the paper's
--   Theorem 4.1, and at `p = 2`, `m = 3` it is Utz's theorem.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L337-L396
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L337-L396

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

theorem SZ.Slice.pick_adm {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ (S.m : ℝ) * S.U) :
    S.PDigit (S.pick w).1 ∧ S.PDigit (S.pick w).2 ∧
      0 ≤ w - S.val (S.pick w) ∧ w - S.val (S.pick w) ≤ S.U := by sorry
