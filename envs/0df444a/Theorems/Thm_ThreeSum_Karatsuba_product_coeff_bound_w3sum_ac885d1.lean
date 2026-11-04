-- Prove2me | Theorems.Thm_ThreeSum_Karatsuba_product_coeff_bound_w3sum_ac885d1
-- name    : ThreeSum.Karatsuba.product_coeff_bound_w3sum_ac885d1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:13:54.189865+00:00
-- url     : https://prove2.me/theorems/6169e093-52c0-46c2-8f9b-8f93f7c9aaf4
-- title:
--   Karatsuba: product coeff bound
-- statement:
--   All true product coefficients have a polynomial value bound, including
--   the implicit zeros outside the stored output.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaBounds.lean#L88-L110
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/KaratsubaBounds.lean#L88-L110

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

theorem ThreeSum.Karatsuba.product_coeff_bound_w3sum_ac885d1 {as bs : List ℤ} {n : ℕ} {U : ℤ}
    (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) (j : ℕ) :
    |(asPolynomial as * asPolynomial bs).coeff j| ≤ 2 * (n : ℤ) * U ^ 2 := by sorry
