-- Prove2me | Theorems.Thm_SZ_pick_fst_mem
-- name    : SZ.pick_fst_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:11:57.37825+00:00
-- url     : https://prove2.me/theorems/2c74f1d8-f97a-45a6-922f-669a68aa935a
-- title:
--   SZ: pick fst mem
-- statement:
--   The digits produced are always `0` or `2`: the even-digit alphabet `Ev₃`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L148-L149
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L148-L149

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

theorem SZ.pick_fst_mem (w : ℝ) : (pick w).1 = 0 ∨ (pick w).1 = 2 := by sorry
