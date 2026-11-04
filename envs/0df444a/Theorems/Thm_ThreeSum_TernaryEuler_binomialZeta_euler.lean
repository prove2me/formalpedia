-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_binomialZeta_euler
-- name    : ThreeSum.TernaryEuler.binomialZeta_euler
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:50.583206+00:00
-- url     : https://prove2.me/theorems/bde07ab7-fd30-4414-97cb-f2669cb2a50c
-- title:
--   Ternary Euler: binomial Zeta euler
-- statement:
--   The Euler denominator uses the source rank, not the output rank.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L72-L84
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L72-L84

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.binomialZeta_euler {N : ℕ} (f : TritWord N → ℤ) (h : ℕ)
    (hf : ∀ A, f A ≠ 0 → rank A = h) (R : TritWord N) :
    (∑ i : Fin N, (R i).val * binomialZeta f (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * binomialZeta f R := by sorry
