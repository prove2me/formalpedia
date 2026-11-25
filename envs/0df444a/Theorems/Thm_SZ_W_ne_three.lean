-- Prove2me | Theorems.Thm_SZ_W_ne_three
-- name    : SZ.W_ne_three
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:28:00.572406+00:00
-- url     : https://prove2.me/theorems/45e38e0b-f22e-46fa-a1c6-1eb07e7ab067
-- title:
--   SZ: W ne three
-- statement:
--   The SZ construction uses the W ne three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L277-L279
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L277-L279

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

theorem SZ.W_ne_three (k : ℕ) : W k ≠ 3 := by sorry
