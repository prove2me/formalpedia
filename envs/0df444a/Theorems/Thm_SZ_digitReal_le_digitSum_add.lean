-- Prove2me | Theorems.Thm_SZ_digitReal_le_digitSum_add
-- name    : SZ.digitReal_le_digitSum_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:23:34.794569+00:00
-- url     : https://prove2.me/theorems/a9f70f99-b1af-4a1d-b34e-664541acad63
-- title:
--   SZ: digit Real le digit Sum add
-- statement:
--   The SZ construction uses the digit Real le digit Sum add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L994-L1003
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverTree.lean#L994-L1003

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.digitReal_le_digitSum_add {m : ℕ} {d : ℕ → ℤ} (h : IsDigits m d) (k : ℕ) :
    digitReal m d ≤ digitSum m d k + 1 / (m : ℝ) ^ k := by sorry
