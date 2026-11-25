-- Prove2me | Theorems.Thm_SZ_Slice_val_pick_W
-- name    : SZ.Slice.val_pick_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:00.678338+00:00
-- url     : https://prove2.me/theorems/df68267f-aaf6-4f6c-9945-f1f3b02f5528
-- title:
--   Slice: val pick W
-- statement:
--   The Slice construction uses the val pick W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L420-L421
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L420-L421

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

theorem SZ.Slice.val_pick_W (w₀ : ℝ) (k : ℕ) :
    S.val (S.pick (S.W w₀ k)) = (S.dA w₀ k : ℝ) + (S.dB w₀ k : ℝ) * S.sq := by sorry
