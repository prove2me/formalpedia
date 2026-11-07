-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalModularCosetPolynomial_top_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalModularCosetPolynomial_top_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:03:18.13155+00:00
-- url     : https://prove2.me/theorems/df9447b4-a2ab-43d4-a8f0-c871052aacf0
-- title:
--   Tanner Lifted Product: lps Original Modular Coset Polynomial top coeff
-- statement:
--   The actual top coefficient of the literal coset product is (-1)^r times genuine Delta norm.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L267-L291
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalJNormalization.lean#L267-L291

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalModularEquation
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalModularCosetPolynomial_top_coeff (N : ℕ) [NeZero N] (hN : 0<N)
    (τ : ℍ) :
    (lpsOriginalModularCosetPolynomial N hN τ).coeff (Nat.card (𝒮ℒ ⧸
      (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))=
      (-1:ℂ)^(Nat.card (𝒮ℒ ⧸
        (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ))*
        lpsOriginalDeltaDilatedNorm N hN τ := by sorry
