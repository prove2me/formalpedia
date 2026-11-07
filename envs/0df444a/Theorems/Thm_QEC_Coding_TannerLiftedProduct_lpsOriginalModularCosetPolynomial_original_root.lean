-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularCosetPolynomial_original_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularCosetPolynomial_original_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:55:02.579868+00:00
-- url     : https://prove2.me/theorems/742a43c8-eb35-49e9-8620-673369844fdd
-- title:
--   Tanner Lifted Product: lps Original Modular Coset Polynomial original root
-- statement:
--   The genuine identity-coset factor makes same original jN a root of the coset product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L194-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L194-L206

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularCosetPolynomial_original_root (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularCosetPolynomial N hN τ).eval (lpsOriginalJDilated N hN τ)=0 := by sorry
