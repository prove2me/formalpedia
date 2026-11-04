-- Prove2me | Theorems.Thm_ThreeSum_Cover_trimmed_support_fraction
-- name    : ThreeSum.Cover.trimmed_support_fraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:04:51.234718+00:00
-- url     : https://prove2.me/theorems/35f4d9f1-1aaa-4118-b864-32d7482867cc
-- title:
--   Cover: trimmed support fraction
-- statement:
--   The explicit 1/(320(mu+1)) support fraction used for a microblock.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L71-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Cover.lean#L71-L84

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

theorem ThreeSum.Cover.trimmed_support_fraction {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℝ) (mu : ℕ) {lam : ℝ} (hlam : 0 < lam)
    (hlower : 1 ≤ 16 * (mu + 1 : ℝ) * lam)
    (hfirst : lam * Fintype.card Ω / 2 ≤ ∑ ω, f ω)
    (hsecond : (∑ ω, (f ω) ^ 2) ≤ 5 * lam * Fintype.card Ω) :
    (Fintype.card Ω : ℝ) ≤
      320 * (mu + 1 : ℝ) * ((univ.filter fun ω => f ω ≠ 0).card : ℝ) := by sorry
