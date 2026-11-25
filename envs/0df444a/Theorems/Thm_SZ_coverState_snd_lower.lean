-- Prove2me | Theorems.Thm_SZ_coverState_snd_lower
-- name    : SZ.coverState_snd_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:08:54.66795+00:00
-- url     : https://prove2.me/theorems/0e3b204f-8953-426c-838a-0f335d8885f7
-- title:
--   SZ: cover State snd lower
-- statement:
--   The SZ construction uses the cover State snd lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L247-L255
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L247-L255

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

theorem SZ.coverState_snd_lower (k : ℕ) : 6 * 3 ^ k + 3 ≤ (coverState k).2 := by sorry
