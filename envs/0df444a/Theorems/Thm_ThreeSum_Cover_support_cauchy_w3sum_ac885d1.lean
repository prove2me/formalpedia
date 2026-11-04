-- Prove2me | Theorems.Thm_ThreeSum_Cover_support_cauchy_w3sum_ac885d1
-- name    : ThreeSum.Cover.support_cauchy_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:50.024194+00:00
-- url     : https://prove2.me/theorems/c09c1180-f03c-4f73-8e33-f99ac6fb8a17
-- title:
--   Cover: support cauchy
-- statement:
--   Cauchy--Schwarz with the cardinality of the actual support.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L26-L47
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L26-L47

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Cover
set_option autoImplicit false
open ThreeSum ThreeSum.Cover
open Finset
open scoped BigOperators

theorem ThreeSum.Cover.support_cauchy_w3sum_ac885d1 {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) :
    (∑ ω, f ω) ^ 2 ≤
      ((univ.filter fun ω => f ω ≠ 0).card : ℝ) * ∑ ω, (f ω) ^ 2 := by sorry
