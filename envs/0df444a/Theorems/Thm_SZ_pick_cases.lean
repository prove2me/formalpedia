-- Prove2me | Theorems.Thm_SZ_pick_cases
-- name    : SZ.pick_cases
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T00:48:16.736117+00:00
-- url     : https://prove2.me/theorems/c5c4dcc4-472c-49c6-a7d3-de3ca4f767eb
-- title:
--   SZ: pick cases
-- statement:
--   The SZ construction uses the pick cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L123-L133
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L123-L133

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

theorem SZ.pick_cases (w : ℝ) :
    (w ≤ 1 + Real.sqrt 3 ∧ pick w = (0, 0)) ∨
    (1 + Real.sqrt 3 < w ∧ w < 2 * Real.sqrt 3 ∧ pick w = (2, 0)) ∨
    (2 * Real.sqrt 3 ≤ w ∧ w ≤ 1 + 3 * Real.sqrt 3 ∧ pick w = (0, 2)) ∨
    (1 + 3 * Real.sqrt 3 < w ∧ pick w = (2, 2)) := by sorry
