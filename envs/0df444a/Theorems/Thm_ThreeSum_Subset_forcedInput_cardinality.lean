-- Prove2me | Theorems.Thm_ThreeSum_Subset_forcedInput_cardinality
-- name    : ThreeSum.Subset.forcedInput_cardinality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:36.23382+00:00
-- url     : https://prove2.me/theorems/63a52396-1a01-4433-878c-a82683e81ee6
-- title:
--   Subset: forced Input cardinality
-- statement:
--   The Subset construction uses the forced Input cardinality property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L409-L427
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L409-L427

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset
set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]

theorem ThreeSum.Subset.forcedInput_cardinality
    (f : Finset α → ℤ) (pre suffix : Finset α) (a : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hd : Disjoint pre suffix) :
    ∀ x, forcedInput f pre suffix x ≠ 0 → x.card = a - pre.card := by sorry
