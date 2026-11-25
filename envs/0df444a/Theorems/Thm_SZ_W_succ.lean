-- Prove2me | Theorems.Thm_SZ_W_succ
-- name    : SZ.W_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:27.111258+00:00
-- url     : https://prove2.me/theorems/f2f85fbf-ad4c-4409-954e-434fadf2b4d9
-- title:
--   SZ: W succ
-- statement:
--   The SZ construction uses the W succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L218-L222
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L218-L222

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

theorem SZ.W_succ (k : ℕ) :
    W (k + 1) = 3 * (W k - ((digitA k : ℝ) + (digitB k : ℝ) * Real.sqrt 3)) := by sorry
