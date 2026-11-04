-- Prove2me | Theorems.Thm_ThreeSum_Subset_zetaStep_stays_in_downset
-- name    : ThreeSum.Subset.zetaStep_stays_in_downset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:34.631201+00:00
-- url     : https://prove2.me/theorems/6f11e13e-a2d1-4369-94b7-eba0b3bfa2bf
-- title:
--   Subset: zeta Step stays in downset
-- statement:
--   The ordinary zeta update also reads only from that same downset.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L400-L403
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L400-L403

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

theorem ThreeSum.Subset.zetaStep_stays_in_downset
    (u : Finset α) (a : α) (mu : ℕ) (h : u.card ≤ mu) :
    (u.erase a).card ≤ mu := by sorry
