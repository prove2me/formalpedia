-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalE4DenominatorCosetPolynomial_coeff
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalE4DenominatorCosetPolynomial_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:21:16.513203+00:00
-- url     : https://prove2.me/theorems/ffad8e3c-ce1c-41d6-b25f-629ebc17b46a
-- title:
--   Tanner Lifted Product: lps Original E4 Denominator Coset Polynomial coeff
-- statement:
--   The actual finite-coset product has the computed E4 denominator top coefficient.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L72-L106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L72-L106

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalE4DenominatorCosetPolynomial_coeff
    (N : ℕ) [NeZero N] (k : ℕ) (A : LPSOriginalMeromorphicLevelForm N k) (τ : ℍ) :
    (lpsOriginalMeromorphicRatioCosetPolynomial N k A
      (lpsOriginalMeromorphicE4PowerAtLevel N k) τ).coeff
      (Nat.card (LPSOriginalMeromorphicCosets N)) =
        (-1 : ℂ)^Nat.card (LPSOriginalMeromorphicCosets N) *
          (ModularForm.E₄ τ^3)^(k * Nat.card (LPSOriginalMeromorphicCosets N)) := by sorry
