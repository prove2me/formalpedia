-- Prove2me | Theorems.Thm_ThreeSum_Karatsuba_coefficient_correct
-- name    : ThreeSum.Karatsuba.coefficient_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:05:26.020035+00:00
-- url     : https://prove2.me/theorems/7c77be88-db9b-454e-9c69-5b04acf3444f
-- title:
--   Karatsuba: coefficient correct
-- statement:
--   The algorithm's output has the ordinary convolution coefficient at
--   every index, not merely the same value at a selected evaluation point.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Karatsuba.lean#L174-L179
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/Karatsuba.lean#L174-L179

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Definitions.Def_Submission_ThreeSum_Karatsuba
set_option autoImplicit false
open ThreeSum ThreeSum.Karatsuba
open Polynomial

theorem ThreeSum.Karatsuba.coefficient_correct (k : ℕ) (as bs : List ℤ)
    (ha : as.length ≤ 2 ^ k) (hb : bs.length ≤ 2 ^ k) (j : ℕ) :
    (asPolynomial (multiply k as bs)).coeff j =
      ∑ p ∈ Finset.antidiagonal j,
        (asPolynomial as).coeff p.1 * (asPolynomial bs).coeff p.2 := by sorry
