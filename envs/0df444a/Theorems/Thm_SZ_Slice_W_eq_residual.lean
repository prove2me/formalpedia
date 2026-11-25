-- Prove2me | Theorems.Thm_SZ_Slice_W_eq_residual
-- name    : SZ.Slice.W_eq_residual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:53:57.89607+00:00
-- url     : https://prove2.me/theorems/eb4b8740-b29b-45a5-b8fd-08117fdaf216
-- title:
--   Slice: W eq residual
-- statement:
--   The residual identity: `W k = m^{k+1} (σ - ⟨a⟩_k - √m ⟨b⟩_k)`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L461-L472
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/Slice.lean#L461-L472

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
variable {S}

theorem SZ.Slice.W_eq_residual (S : Slice) (σ : ℝ) (k : ℕ) :
    S.W ((S.m : ℝ) * σ) k = (S.m : ℝ) ^ (k + 1) *
      (σ - digitSum S.m (S.dA ((S.m : ℝ) * σ)) k
         - S.sq * digitSum S.m (S.dB ((S.m : ℝ) * σ)) k) := by sorry
