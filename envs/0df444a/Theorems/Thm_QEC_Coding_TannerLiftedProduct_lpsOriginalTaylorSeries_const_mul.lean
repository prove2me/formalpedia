-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalTaylorSeries_const_mul
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_const_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:55:50.626595+00:00
-- url     : https://prove2.me/theorems/6ee6fa05-15ce-4410-9b3d-a8d1f547fc9c
-- title:
--   Tanner Lifted Product: lps Original Taylor Series const mul
-- statement:
--   Actual Taylor series under complex constant multiplication from derivative linearity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L126-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L126-L130

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalQExpansionArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalJNormalization
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PowerSeries.Expand
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRationalModularEquation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalTaylorSeries_const_mul (c : ℂ) (f : ℂ→ℂ) :
    lpsOriginalTaylorSeries (fun q=>c*f q)=PowerSeries.C c*lpsOriginalTaylorSeries f := by sorry
