-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionField_finiteDimensional
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:56:29.572692+00:00
-- url     : https://prove2.me/theorems/e12dc55b-b86a-4926-8de3-e207fb2588a0
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field finite Dimensional
-- statement:
--   Actual finite dimensionality of the literally generated SAME C(j,jN) field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L196-L201
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalFunctionField.lean#L196-L201

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionField_finiteDimensional (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    FiniteDimensional (FractionRing (Polynomial ℂ)) (lpsOriginalGeneratedFunctionField N hN) := by sorry
