-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_main
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.main
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:27:06.480683+00:00
-- url     : https://prove2.me/theorems/215a37cc-9b2c-5d93-a57e-34387c3b02fc
-- title:
--   Simplex Sum: main
-- statement:
--   The Simplex Sum construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L67-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L67-L111

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_AsymptoticSequences_SimplexSumSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Filter Asymptotics Finset
open ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum

theorem ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.main (j : ℕ) : ∀ i : ℕ, (fun n : ℕ => S i j n / ((i.factorial : ℝ) * (j.factorial : ℝ)) -
      (n : ℝ) ^ (i + j + 1) / ((i + j + 1).factorial : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (i + j) := by sorry
