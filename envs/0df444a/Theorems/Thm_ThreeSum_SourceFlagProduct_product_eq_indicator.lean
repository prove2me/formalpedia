-- Prove2me | Theorems.Thm_ThreeSum_SourceFlagProduct_product_eq_indicator
-- name    : ThreeSum.SourceFlagProduct.product_eq_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:23:05.427446+00:00
-- url     : https://prove2.me/theorems/3b4c2180-ee54-4e97-b6a6-aa40667855f2
-- title:
--   Source Flag Product: product eq indicator
-- statement:
--   The Source Flag Product construction uses the product eq indicator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFlagProduct.lean#L41-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SourceFlagProduct.lean#L41-L51

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_SourceFlagProduct
set_option autoImplicit false
open ThreeSum ThreeSum.SourceFlagProduct
open Finset
open scoped BigOperators

theorem ThreeSum.SourceFlagProduct.product_eq_indicator (flag : ℕ → ℕ) (n : ℕ) (p : Prop) [Decidable p]
    (hflag : ∀ i < n, flag i ≤ 1) (hp : (∀ i < n, flag i=1) ↔ p) :
    product flag n = if p then 1 else 0 := by sorry
