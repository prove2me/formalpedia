-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalGeneratedFunctionFieldQ_finiteDimensional
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:59:19.049199+00:00
-- url     : https://prove2.me/theorems/639e71da-75ec-46dd-9c75-7dba7f34427f
-- title:
--   Tanner Lifted Product: lps Original Generated Function Field Q finite Dimensional
-- statement:
--   Finite dimensionality of the literal SAME original rational generated field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L162-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalFunctionField.lean#L162-L167

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFunctionField
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalFunctionField
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalGeneratedFunctionFieldQ_finiteDimensional (N : ℕ) [NeZero N] (hN : 0<N) :
    letI := lpsOriginalJFractionEmbeddingQ.toAlgebra
    FiniteDimensional (FractionRing (Polynomial ℚ)) (lpsOriginalGeneratedFunctionFieldQ N hN) := by sorry
