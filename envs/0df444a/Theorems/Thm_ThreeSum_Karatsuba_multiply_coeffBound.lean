-- Prove2me | Theorems.Thm_ThreeSum_Karatsuba_multiply_coeffBound
-- name    : ThreeSum.Karatsuba.multiply_coeffBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:14:00.116857+00:00
-- url     : https://prove2.me/theorems/a16ed05f-a10b-48ec-85b3-09dc47422ad6
-- title:
--   Karatsuba: multiply coeff Bound
-- statement:
--   The Karatsuba construction uses the multiply coeff Bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaBounds.lean#L112-L118
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaBounds.lean#L112-L118

import Definitions.Def_Submission_ThreeSum_Karatsuba
import Mathlib.Data.List.GetD
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial
open scoped BigOperators

theorem ThreeSum.Karatsuba.multiply_coeffBound {as bs : List ℤ} {k : ℕ} {U : ℤ}
    (ha : as.length ≤ 2 ^ k) (hb : bs.length ≤ 2 ^ k)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) :
    CoeffBound (multiply k as bs) (2 * (2 ^ k : ℕ) * U ^ 2) := by sorry
