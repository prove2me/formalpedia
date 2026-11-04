-- Prove2me | Theorems.Thm_ThreeSum_Subset_unionConvolution_eq_disjointConvolution_w3sum_ac885d1
-- name    : ThreeSum.Subset.unionConvolution_eq_disjointConvolution_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:23.301742+00:00
-- url     : https://prove2.me/theorems/d6c62faf-9aaa-4b9f-99f3-d7f8587e3989
-- title:
--   Subset: union Convolution eq disjoint Convolution
-- statement:
--   The Subset construction uses the union Convolution eq disjoint Convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L191-L239
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L191-L239

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

theorem ThreeSum.Subset.unionConvolution_eq_disjointConvolution_w3sum_ac885d1
    (f g : Finset α → ℤ) (q : Finset α) (a b : ℕ)
    (hf : ∀ s, f s ≠ 0 → s.card = a)
    (hg : ∀ v, g v ≠ 0 → v.card = b)
    (hq : q.card = a + b) :
    unionConvolution f g q = disjointConvolution f g q := by sorry
