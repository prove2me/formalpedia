-- Prove2me | Theorems.Thm_ThreeSum_Subset_mobius_zeta_w3sum_ac885d1
-- name    : ThreeSum.Subset.mobius_zeta_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:19.585532+00:00
-- url     : https://prove2.me/theorems/eed62518-3b62-4782-abfc-38f0ad899ca8
-- title:
--   Subset: mobius zeta
-- statement:
--   Exact Möbius inversion. The proof is induction on the finite output set.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L81-L94
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L81-L94

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

theorem ThreeSum.Subset.mobius_zeta_w3sum_ac885d1 (f : Finset α → ℤ) (q : Finset α) :
    mobius (zeta f) q = f q := by sorry
