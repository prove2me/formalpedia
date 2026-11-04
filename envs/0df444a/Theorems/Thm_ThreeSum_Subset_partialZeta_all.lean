-- Prove2me | Theorems.Thm_ThreeSum_Subset_partialZeta_all
-- name    : ThreeSum.Subset.partialZeta_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:26.67212+00:00
-- url     : https://prove2.me/theorems/7233eb33-ddf0-4157-ab77-cbfb68d3aa24
-- title:
--   Subset: partial Zeta all
-- statement:
--   The Subset construction uses the partial Zeta all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L296-L298
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L296-L298

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

theorem ThreeSum.Subset.partialZeta_all (f : Finset α → ℤ) (u : Finset α) :
    partialZeta u f u = zeta f u := by sorry
