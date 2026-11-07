-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedRationalCusp_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:05:54.851513+00:00
-- url     : https://prove2.me/theorems/140b2729-1e27-4506-82ac-50a67c11df91
-- title:
--   Tanner Lifted Product: lps Original Cleared Rational Cusp taylor
-- statement:
--   Genuine Taylor series of the finite rational cleared cusp function.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L419-L436
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L419-L436

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedRationalCusp_taylor (N : ℕ) (hN : N≠0) (B : ℕ)
    (P : Polynomial (Polynomial ℂ)) :
    lpsOriginalTaylorSeries (lpsOriginalClearedRationalCusp N B P)=
      PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormal N hN B P) := by sorry
