-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finrank_bound
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_finrank_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:02:02.505449+00:00
-- url     : https://prove2.me/theorems/4ad28da0-07c1-4613-8007-25c95e0804ce
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field finrank bound
-- statement:
--   Actual generated-field degree upper bound via its genuine minimal polynomial dividing the proved monic annihilator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L204-L215
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L204-L215

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_finrank_bound (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    Module.finrank (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN)≤
      Nat.card (𝒮ℒ ⧸ (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) := by sorry
