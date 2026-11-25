-- Prove2me | Theorems.Thm_SZ_W_mem
-- name    : SZ.W_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:12.061549+00:00
-- url     : https://prove2.me/theorems/16f13a3b-3602-49fd-a020-e4d3342db975
-- title:
--   SZ: W mem
-- statement:
--   **The invariant** (Cover Lemma, by induction): the state never leaves `[0, 3U]`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L235-L243
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L235-L243

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

theorem SZ.W_mem (k : ℕ) : 0 ≤ W k ∧ W k ≤ 3 + 3 * Real.sqrt 3 := by sorry
