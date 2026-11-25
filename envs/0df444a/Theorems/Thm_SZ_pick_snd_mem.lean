-- Prove2me | Theorems.Thm_SZ_pick_snd_mem
-- name    : SZ.pick_snd_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:26:47.690459+00:00
-- url     : https://prove2.me/theorems/250fa84d-b895-42b8-ac7f-83474da39c28
-- title:
--   SZ: pick snd mem
-- statement:
--   The SZ construction uses the pick snd mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L151-L152
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L151-L152

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

theorem SZ.pick_snd_mem (w : ℝ) : (pick w).2 = 0 ∨ (pick w).2 = 2 := by sorry
