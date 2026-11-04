-- Prove2me | Theorems.Thm_ThreeSum_Karatsuba_multiply_correct
-- name    : ThreeSum.Karatsuba.multiply_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:05:25.460228+00:00
-- url     : https://prove2.me/theorems/8616f4ed-bb19-4de8-aea7-1a4666dfbb69
-- title:
--   Karatsuba: multiply correct
-- statement:
--   All coefficients of the computed product are correct.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Karatsuba.lean#L143-L170
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Karatsuba.lean#L143-L170

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Karatsuba
set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.Karatsuba.multiply_correct (k : ℕ) (as bs : List ℤ)
    (ha : as.length ≤ 2 ^ k) (hb : bs.length ≤ 2 ^ k) :
    asPolynomial (multiply k as bs) = asPolynomial as * asPolynomial bs := by sorry
