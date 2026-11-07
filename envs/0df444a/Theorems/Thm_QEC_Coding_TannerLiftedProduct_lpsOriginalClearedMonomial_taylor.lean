-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_taylor
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedMonomial_taylor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:57:17.284547+00:00
-- url     : https://prove2.me/theorems/254319bd-b2db-465e-972a-98770bd4d3c9
-- title:
--   Tanner Lifted Product: lps Original Cleared Monomial taylor
-- statement:
--   Actual cleared cusp monomial Taylor identity with its concrete rational formal counterpart.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L330-L346
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L330-L346

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedMonomial_taylor (N : ℕ) (hN : N≠0) (B i k : ℕ) :
    lpsOriginalTaylorSeries (lpsOriginalClearedMonomial N B i k)=
      PowerSeries.map (algebraMap ℚ ℂ) (lpsOriginalClearedFormalMonomial N hN B i k) := by sorry
