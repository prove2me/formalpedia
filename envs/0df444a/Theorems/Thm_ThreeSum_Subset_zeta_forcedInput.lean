-- Prove2me | Theorems.Thm_ThreeSum_Subset_zeta_forcedInput
-- name    : ThreeSum.Subset.zeta_forcedInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:37.9626+00:00
-- url     : https://prove2.me/theorems/507bf2af-c889-464d-9a0b-8f1a57a8720c
-- title:
--   Subset: zeta forced Input
-- statement:
--   The Subset construction uses the zeta forced Input property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L429-L438
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L429-L438

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

theorem ThreeSum.Subset.zeta_forcedInput
    (f : Finset α → ℤ) (pre suffix t : Finset α)
    (hd : Disjoint pre suffix) (ht : t ⊆ suffix) :
    zeta (forcedInput f pre suffix) t =
      partialZeta suffix f (pre ∪ t) := by sorry
