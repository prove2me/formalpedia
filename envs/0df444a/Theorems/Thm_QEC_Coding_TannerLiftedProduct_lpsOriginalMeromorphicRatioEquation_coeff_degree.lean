-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalMeromorphicRatioEquation_coeff_degree
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_coeff_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:21:00.005145+00:00
-- url     : https://prove2.me/theorems/f2c3da24-d9e5-4fdf-bbb5-ebc6fc81cdc2
-- title:
--   Tanner Lifted Product: lps Original Meromorphic Ratio Equation coeff degree
-- statement:
--   Every inner coefficient of the actual finite-coset equation has the genuine common degree bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L22-L35
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L22-L35

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalMeromorphicRatioEquation_coeff_degree
    (N : ℕ) [NeZero N] (k : ℕ) (A B : LPSOriginalMeromorphicLevelForm N k)
    (n : ℕ) :
    ((lpsOriginalMeromorphicRatioEquation N k A B).coeff n).natDegree ≤
      k * Nat.card (LPSOriginalMeromorphicCosets N) := by sorry
