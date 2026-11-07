-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRationalSeriesRetraction_zero
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeriesRetraction_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:58:34.842205+00:00
-- url     : https://prove2.me/theorems/ee49d4ae-35a9-41a9-9a10-d85987757c3d
-- title:
--   Tanner Lifted Product: lps Original Rational Series Retraction zero
-- statement:
--   The coefficientwise transfer sends the actual zero series to zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L74-L77
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L74-L77

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRationalSeriesRetraction_zero :
    lpsOriginalRationalSeriesRetraction 0=0 := by sorry
