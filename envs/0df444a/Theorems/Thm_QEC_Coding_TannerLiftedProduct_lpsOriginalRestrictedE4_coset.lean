-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRestrictedE4_coset
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalRestrictedE4_coset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:21:50.350555+00:00
-- url     : https://prove2.me/theorems/e2583bbc-6126-4e85-bdcd-624369b14c14
-- title:
--   Tanner Lifted Product: lps Original Restricted E4 coset
-- statement:
--   Every actual SL2 coset translate of the E4 denominator has the same value.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L58-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L58-L69

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

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalRestrictedE4_coset (N k : ℕ)
    (q : LPSOriginalMeromorphicCosets N) (τ : ℍ) :
    SlashInvariantForm.quotientFunc
      (lpsOriginalMeromorphicE4PowerAtLevel N k) q τ =
      (ModularForm.E₄ τ^3)^k := by sorry
