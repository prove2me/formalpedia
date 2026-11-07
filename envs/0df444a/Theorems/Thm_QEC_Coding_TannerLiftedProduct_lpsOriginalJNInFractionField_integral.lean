-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJNInFractionField_integral
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:56:23.928108+00:00
-- url     : https://prove2.me/theorems/56975596-495c-40d2-b3d4-896c4dd38253
-- title:
--   Tanner Lifted Product: lps Original JNIn Fraction Field integral
-- statement:
--   Actual integrality of SAME original jN over the embedded C(j) fraction field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L188-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L188-L193

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJNInFractionField_integral (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    IsIntegral (FractionRing (Polynomial ℂ)) (lpsOriginalJNInFractionField N hN) := by sorry
