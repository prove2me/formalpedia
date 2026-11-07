-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalClearedMonomial_analytic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalClearedMonomial_analytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:56:01.52521+00:00
-- url     : https://prove2.me/theorems/1c965f7a-2dea-494b-baff-834f84f6d488
-- title:
--   Tanner Lifted Product: lps Original Cleared Monomial analytic
-- statement:
--   Actual cleared cusp monomial analyticity for every positive level.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L322-L327
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalRationalModularEquation.lean#L322-L327

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalClearedMonomial_analytic (N : ℕ) (hN : N≠0) (B i k : ℕ) :
    AnalyticAt ℂ (lpsOriginalClearedMonomial N B i k) 0 := by sorry
