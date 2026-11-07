-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularEquationComplex_recovery
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:51:54.821237+00:00
-- url     : https://prove2.me/theorems/eba998d2-f36f-41a7-a314-44f6877ddf35
-- title:
--   Tanner Lifted Product: lps Original Modular Equation Complex recovery
-- statement:
--   Actual Delta^r times the fixed original equation specializes to the literal coset product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L279-L309
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L279-L309

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularEquationComplex_recovery (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    Polynomial.C (ModularForm.discriminant τ^(Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)))*
      (lpsOriginalModularEquationComplex N hN).map
        (Polynomial.evalRingHom (lpsOriginalJInvariant τ))=
      lpsOriginalModularCosetPolynomial N hN τ := by sorry
