-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalHolomorphicJFraction_coefficient
-- name    : QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicJFraction_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:22:23.012707+00:00
-- url     : https://prove2.me/theorems/45120dc9-f0cd-484c-a10d-89220eb01654
-- title:
--   Tanner Lifted Product: lps Original Holomorphic JFraction coefficient
-- statement:
--   The actual j coefficient map into the holomorphic fraction field is literal polynomial evaluation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L253-L261
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSOriginalReciprocalE4Equation.lean#L253-L261

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ReciprocalPolynomialCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicIntegral
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalHolomorphicFractionRoot
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationChartEvaluation
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalReciprocalE4Equation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular
noncomputable section
local notation "R" => LPSOriginalHolomorphicRing
local notation "H" => LPSOriginalHolomorphicFractionField
local notation "P" => Polynomial ℂ

theorem QEC.Coding.TannerLiftedProduct.lpsOriginalHolomorphicJFraction_coefficient :
    (algebraMap R H).comp lpsOriginalJHolomorphicEval.toRingHom =
      Polynomial.eval₂RingHom ((algebraMap R H).comp (algebraMap ℂ R))
        (algebraMap R H lpsOriginalJHolomorphic) := by sorry
