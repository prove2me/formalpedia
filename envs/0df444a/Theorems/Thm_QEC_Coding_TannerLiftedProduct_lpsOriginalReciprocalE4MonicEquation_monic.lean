-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalReciprocalE4MonicEquation_monic
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalE4MonicEquation_monic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:26:46.111642+00:00
-- url     : https://prove2.me/theorems/f41a1ebf-975c-4bec-a2ee-0287f55ba4f1
-- title:
--   Tanner Lifted Product: lps Original Reciprocal E4 Monic Equation monic
-- statement:
--   The constructed reciprocal equation is genuinely monic in the unchanged function variable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L161-L175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L161-L175

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalReciprocalE4MonicEquation_monic
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) :
    (lpsOriginalReciprocalE4MonicEquation N k A).Monic := by sorry
