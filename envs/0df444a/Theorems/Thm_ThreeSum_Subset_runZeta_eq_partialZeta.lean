-- Prove2me | Theorems.Thm_ThreeSum_Subset_runZeta_eq_partialZeta
-- name    : ThreeSum.Subset.runZeta_eq_partialZeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:29.653771+00:00
-- url     : https://prove2.me/theorems/3c1be676-c25d-4831-b0b3-beb0bf65fd9a
-- title:
--   Subset: run Zeta eq partial Zeta
-- statement:
--   The Subset construction uses the run Zeta eq partial Zeta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L354-L366
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L354-L366

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

theorem ThreeSum.Subset.runZeta_eq_partialZeta (coords : List α) (hn : coords.Nodup)
    (f : Finset α → ℤ) (u : Finset α) :
    runZeta coords f u = partialZeta coords.toFinset f u := by sorry
