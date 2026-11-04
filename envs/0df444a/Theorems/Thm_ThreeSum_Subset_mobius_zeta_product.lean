-- Prove2me | Theorems.Thm_ThreeSum_Subset_mobius_zeta_product
-- name    : ThreeSum.Subset.mobius_zeta_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:17:21.410006+00:00
-- url     : https://prove2.me/theorems/5981ac42-98b8-429c-a1f1-db4d3c510b89
-- title:
--   Subset: mobius zeta product
-- statement:
--   The signed product of two ordinary zeta transforms counts exact unions.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L174-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Subset.lean#L174-L179

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

theorem ThreeSum.Subset.mobius_zeta_product (f g : Finset α → ℤ) (q : Finset α) :
    mobius (fun t => zeta f t * zeta g t) q = unionConvolution f g q := by sorry
