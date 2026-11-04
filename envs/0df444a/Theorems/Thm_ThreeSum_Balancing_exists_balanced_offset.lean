-- Prove2me | Theorems.Thm_ThreeSum_Balancing_exists_balanced_offset
-- name    : ThreeSum.Balancing.exists_balanced_offset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:34.584734+00:00
-- url     : https://prove2.me/theorems/15bd84a2-dea4-4afc-8834-470da64fe0e3
-- title:
--   Balancing: exists balanced offset
-- statement:
--   The mean is exact for every table, with no hash-uniformity assumption.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Balancing.lean#L32-L39
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Balancing.lean#L32-L39

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_Balancing
set_option autoImplicit false
open ThreeSum ThreeSum.Balancing
open Finset
open scoped BigOperators
variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem ThreeSum.Balancing.exists_balanced_offset (F H : G → ℕ) :
    ∃ d, Fintype.card G * correlation F H d ≤ (∑ k, F k) * (∑ k, H k) := by sorry
