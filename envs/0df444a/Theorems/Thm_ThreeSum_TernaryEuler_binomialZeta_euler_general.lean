-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_binomialZeta_euler_general
-- name    : ThreeSum.TernaryEuler.binomialZeta_euler_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:52.627149+00:00
-- url     : https://prove2.me/theorems/5b958293-3b0f-4bfb-a656-f6d5c0cc45b2
-- title:
--   Ternary Euler: binomial Zeta euler general
-- statement:
--   The Ternary Euler construction uses the binomial Zeta euler general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L61-L69
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L61-L69

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.binomialZeta_euler_general {N : ℕ} (f : TritWord N → ℤ) (R : TritWord N) :
    (∑ i : Fin N, (R i).val * binomialZeta f (predecessor R i)) =
      ∑ A : TritWord N, ((rank R : ℤ) - (rank A : ℤ)) * weight R A * f A := by sorry
