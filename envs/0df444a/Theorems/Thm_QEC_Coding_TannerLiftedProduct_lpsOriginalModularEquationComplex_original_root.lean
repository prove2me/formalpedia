-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_original_root
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_original_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:53:30.941034+00:00
-- url     : https://prove2.me/theorems/35996a9b-ff5d-46ea-8e15-89d76d48cbcf
-- title:
--   Tanner Lifted Product: lps Original Modular Equation Complex original root
-- statement:
--   The fixed original complex equation vanishes on the same actual j and jN at every tau.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L312-L322
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L312-L322

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_original_root (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularEquationComplex N hN).eval₂
      (Polynomial.evalRingHom (lpsOriginalJInvariant τ)) (lpsOriginalJDilated N hN τ)=0 := by sorry
