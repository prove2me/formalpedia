-- Prove2me | Theorems.Thm_SZ_coverState_succ
-- name    : SZ.coverState_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:26:49.315851+00:00
-- url     : https://prove2.me/theorems/61e0f043-3a18-4423-ad60-fbae1c587023
-- title:
--   SZ: cover State succ
-- statement:
--   The SZ construction uses the cover State succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L211-L213
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L211-L213

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
set_option autoImplicit false
open SZ
open Filter Topology

theorem SZ.coverState_succ (k : ℕ) :
    coverState (k + 1) = (3 * ((coverState k).1 - digitA k), 3 * ((coverState k).2 - digitB k)) := by sorry
