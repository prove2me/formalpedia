-- Prove2me | Theorems.Thm_ThreeSum_TernaryEuler_euler_unique_from_bank
-- name    : ThreeSum.TernaryEuler.euler_unique_from_bank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:37:56.561755+00:00
-- url     : https://prove2.me/theorems/bc6957ed-6c18-430c-b9c4-011e8da0ec13
-- title:
--   Ternary Euler: euler unique from bank
-- statement:
--   Values on the rank bank uniquely determine a homogeneous binomial transform.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L126-L154
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryEuler.lean#L126-L154

import Definitions.Def_Submission_ThreeSum_TernaryQuery
import Definitions.Def_Submission_ThreeSum_TernaryEuler
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEuler
open Finset
open ThreeSum.TernaryJointType ThreeSum.TernaryBank

theorem ThreeSum.TernaryEuler.euler_unique_from_bank {N h T : ℕ} (hcut : h ≤ T)
    (F G : TritWord N → ℤ)
    (hF : ∀ R, (∑ i : Fin N, (R i).val * F (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * F R)
    (hG : ∀ R, (∑ i : Fin N, (R i).val * G (predecessor R i)) =
      ((rank R : ℤ) - (h : ℤ)) * G R)
    (hbank : ∀ R ∈ bank N T, F R = G R) : F = G := by sorry
