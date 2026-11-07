-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularCosetPolynomial_degree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularCosetPolynomial_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:53:06.408914+00:00
-- url     : https://prove2.me/theorems/1eed6bab-239f-473b-9745-cd101eac0c44
-- title:
--   Tanner Lifted Product: lps Original Modular Coset Polynomial degree
-- statement:
--   Actual coset-product polynomial degree is at most its genuine finite coset cardinal.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L209-L227
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalModularEquation.lean#L209-L227

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJPolynomial
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex UpperHalfPlane ModularForm ModularFormClass SlashInvariantFormClass MatrixGroups
open scoped ModularForm UpperHalfPlane
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularCosetPolynomial_degree (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularCosetPolynomial N hN τ).natDegree≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by sorry
