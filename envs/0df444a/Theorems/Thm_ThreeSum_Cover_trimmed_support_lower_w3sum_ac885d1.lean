-- Prove2me | Theorems.Thm_ThreeSum_Cover_trimmed_support_lower_w3sum_ac885d1
-- name    : ThreeSum.Cover.trimmed_support_lower_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:52.66209+00:00
-- url     : https://prove2.me/theorems/4a2c9d19-5950-4da0-b1f7-a17804dca94c
-- title:
--   Cover: trimmed support lower
-- statement:
--   The trimmed second-moment estimate, without division or probabilities.
--   If the first moment is at least lambda/2 and the second at most 5 lambda,
--   at least a lambda/20 fraction of the finite sample space is nonzero.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L52-L68
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L52-L68

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

theorem ThreeSum.Cover.trimmed_support_lower_w3sum_ac885d1 {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hfirst : lam * Fintype.card Ω / 2 ≤ ∑ ω, f ω)
    (hsecond : (∑ ω, (f ω) ^ 2) ≤ 5 * lam * Fintype.card Ω) :
    lam * Fintype.card Ω ≤
      20 * ((univ.filter fun ω => f ω ≠ 0).card : ℝ) := by sorry
