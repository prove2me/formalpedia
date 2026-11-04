-- Prove2me | Theorems.Thm_ThreeSum_Cover_survivor_step
-- name    : ThreeSum.Cover.survivor_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:56.141584+00:00
-- url     : https://prove2.me/theorems/21c76a11-fc4a-4aca-92ea-3208ddee6e7b
-- title:
--   Cover: survivor step
-- statement:
--   An exact survivor recurrence after choosing a good map.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L112-L119
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L112-L119

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Cover
set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators

theorem ThreeSum.Cover.survivor_step {U : Type*} [DecidableEq U]
    (targets : Finset U) (covers : U → Prop) [DecidablePred covers]
    (a : ℕ) (ha : 0 < a)
    (hgood : targets.card ≤ a * (targets.filter covers).card) :
    a * (targets.filter fun u => ¬ covers u).card ≤ (a - 1) * targets.card := by sorry
