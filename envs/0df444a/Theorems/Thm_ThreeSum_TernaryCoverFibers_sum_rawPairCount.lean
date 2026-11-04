-- Prove2me | Theorems.Thm_ThreeSum_TernaryCoverFibers_sum_rawPairCount
-- name    : ThreeSum.TernaryCoverFibers.sum_rawPairCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:44:24.298982+00:00
-- url     : https://prove2.me/theorems/e1579366-9c03-492e-a3e8-faa4cfbd78a6
-- title:
--   Ternary Cover Fibers: sum raw Pair Count
-- statement:
--   Partition the edges at one sum hash by their first endpoint hash.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean#L33-L51
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverFibers.lean#L33-L51

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverFibers
open Finset
open scoped BigOperators
variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
variable [DecidableEq Q] [DecidableEq K] [AddCommGroup K]

theorem ThreeSum.TernaryCoverFibers.sum_rawPairCount (left right : E → K) (o : K) :
    (∑ a : K, rawPairCount left right a (o - a)) =
      (univ.filter fun e => left e + right e = o).card := by sorry
