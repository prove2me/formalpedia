-- Prove2me | Theorems.Thm_P2M_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval__add_smul_idempotent_187145e154d3
-- name    : P2M_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval__add_smul_idempotent_187145e154d3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:46:19.166543+00:00
-- url     : https://prove2.me/theorems/01f3d870-60d6-4291-86e7-591ba55fb7d2
-- title:
--   P2 M QEC Coding Tanner Lifted Product lps Hecke Polynomial eval  add smul idempotent 187145e154d3: P2 M QEC Coding Tanner Lifted Product lps Hecke Polynomial eval  add smul idempotent 187145e154d3
-- statement:
--   Adding a scalar multiple of an orthogonal idempotent changes a Hecke
--   polynomial only by the difference of its scalar evaluations on that
--   idempotent.  This is the algebraic mechanism for removing the constant
--   eigenmode of a regular graph.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L152-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePolynomial.lean#L152-L175

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.RingTheory.Polynomial.Dickson
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePolynomial
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Polynomial

theorem P2M_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval__add_smul_idempotent_187145e154d3
    {A : Type*} [Ring A] [Algebra ℂ A]
    (p d : ℂ) (x e : A)
    (hxe : x * e = 0) (hex : e * x = 0) (hee : e * e = e) : ∀ n : ℕ,
    (lpsHeckePolynomial ℂ p n).eval₂ (algebraMap ℂ A) (x + d • e) =
      (lpsHeckePolynomial ℂ p n).eval₂ (algebraMap ℂ A) x +
        ((lpsHeckePolynomial ℂ p n).eval d -
          (lpsHeckePolynomial ℂ p n).eval 0) • e
  := by sorry

alias «QEC».«Coding».«TannerLiftedProduct».«lpsHeckePolynomial_eval₂_add_smul_idempotent» := P2M_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval__add_smul_idempotent_187145e154d3
