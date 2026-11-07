-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalJQSeries_dilated_map
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalJQSeries_dilated_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:11.480623+00:00
-- url     : https://prove2.me/theorems/50fc1593-c248-4ddb-9151-774d0ad1a95a
-- title:
--   Tanner Lifted Product: lps Original JQSeries dilated map
-- statement:
--   The SAME rational K series expanded by every positive level maps to actual Taylor K(q^N).
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L204-L208
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L204-L208

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalJQSeries_dilated_map (N : ℕ) (hN : N≠0) :
    PowerSeries.map (algebraMap ℚ ℂ) (PowerSeries.expand N hN lpsOriginalJQSeries)=
      lpsOriginalTaylorSeries (fun q=>lpsOriginalJQCoefficient (q^N)) := by sorry
