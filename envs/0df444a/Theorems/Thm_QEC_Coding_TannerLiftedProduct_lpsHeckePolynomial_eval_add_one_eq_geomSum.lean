-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_add_one_eq_geomSum
-- name    : QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_add_one_eq_geomSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:15.184215+00:00
-- url     : https://prove2.me/theorems/20c2d86d-22b5-4bb4-b170-5518ca8c9508
-- title:
--   Tanner Lifted Product: lps Hecke Polynomial eval add one eq geom Sum
-- statement:
--   At the trivial adjacency eigenvalue `p + 1`, the `n`-th LPS Hecke
--   polynomial is the geometric sum `1 + p + ... + p^n`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L93-L105
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L93-L105

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_add_one_eq_geomSum
    (R : Type*) [CommRing R] (p : R) : ∀ n : ℕ,
    (lpsHeckePolynomial R p n).eval (p + 1) =
      ∑ i ∈ Finset.range (n + 1), p ^ i
  := by sorry
