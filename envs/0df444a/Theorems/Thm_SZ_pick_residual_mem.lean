-- Prove2me | Theorems.Thm_SZ_pick_residual_mem
-- name    : SZ.pick_residual_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:57:21.636801+00:00
-- url     : https://prove2.me/theorems/1c10794f-20a4-4917-9519-ed3b8399dd2f
-- title:
--   SZ: pick residual mem
-- statement:
--   **The Cover Lemma at `m = 3`** ([Utz51]; plan §1.3).  Whatever the state `w ∈ [0, 3U]`,
--   the chosen offset lands the residual back in `[0, U]`.  The four gap inequalities are
--   `2 ≤ U`, `2√3 - 2 ≤ U`, `2 + 2√3 - 2√3 ≤ U`, and the top identity `2 + 2√3 + U = 3U`.
--
--   Source: https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L182-L186
-- source:
--   https://github.com/rwst/Square-Roots/blob/e3184902f13967b9f20f37244b3d1c30610ca846/SZ/CoverGame.lean#L182-L186

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

theorem SZ.pick_residual_mem {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 3 + 3 * Real.sqrt 3) :
    0 ≤ w - (((pick w).1 : ℝ) + ((pick w).2 : ℝ) * Real.sqrt 3) ∧
      w - (((pick w).1 : ℝ) + ((pick w).2 : ℝ) * Real.sqrt 3) ≤ 1 + Real.sqrt 3 := by sorry
