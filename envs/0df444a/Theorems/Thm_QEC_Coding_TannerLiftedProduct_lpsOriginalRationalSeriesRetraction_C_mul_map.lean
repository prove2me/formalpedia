-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_C_mul_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeriesRetraction_C_mul_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:59:13.508203+00:00
-- url     : https://prove2.me/theorems/3d3f08d6-883d-4a52-aec7-6f469fa6727f
-- title:
--   Tanner Lifted Product: lps Original Rational Series Retraction C mul map
-- statement:
--   Finite coefficient-convolution transfer of a complex constant times a mapped rational series.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L80-L87
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L80-L87

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeriesRetraction_C_mul_map (c : ℂ) (S : PowerSeries ℚ) :
    lpsOriginalRationalSeriesRetraction
      (PowerSeries.C c*PowerSeries.map (algebraMap ℚ ℂ) S)=
        PowerSeries.C (lpsOriginalRationalRetraction c)*S := by sorry
