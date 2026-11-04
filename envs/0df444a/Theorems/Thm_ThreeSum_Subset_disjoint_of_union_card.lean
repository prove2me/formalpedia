-- Prove2me | Theorems.Thm_ThreeSum_Subset_disjoint_of_union_card
-- name    : ThreeSum.Subset.disjoint_of_union_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:26.239196+00:00
-- url     : https://prove2.me/theorems/c902d248-eab0-4ad5-b29c-fe64de2373d5
-- title:
--   Subset: disjoint of union card
-- statement:
--   If the input sizes add to the output size, an exact union is disjoint.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L182-L185
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L182-L185

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

theorem ThreeSum.Subset.disjoint_of_union_card {s v q : Finset α}
    (hu : s ∪ v = q) (hc : q.card = s.card + v.card) : Disjoint s v := by sorry
