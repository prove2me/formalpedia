-- Prove2me | Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_SimplexSum_S_succ
-- name    : ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.S_succ
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:52:19.338743+00:00
-- url     : https://prove2.me/theorems/a2f03133-e234-5904-b0ee-5a64a67ab9db
-- title:
--   Simplex Sum: S succ
-- statement:
--   The Simplex Sum construction uses the S succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/GeometryOfNumbers/AsymptoticSequences/SimplexSumSt.lean#L58-L65

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

theorem ReciprocityTheory.GeometryOfNumbersTheory.SimplexSum.S_succ (i j n : ℕ) : S i (j + 1) n = n * S i j n - S (i + 1) j n := by sorry
