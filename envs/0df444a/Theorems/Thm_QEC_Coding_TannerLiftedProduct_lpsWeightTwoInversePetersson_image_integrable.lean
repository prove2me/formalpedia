-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoInversePetersson_image_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoInversePetersson_image_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:57:17.575365+00:00
-- url     : https://prove2.me/theorems/71f5a97f-8402-486d-95ed-cef95dca39e4
-- title:
--   Tanner Lifted Product: lps Weight Two Inverse Petersson image integrable
-- statement:
--   The positive-determinant inverse-matrix image integral is separately absolutely convergent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L73-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L73-L80

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoInversePetersson_image_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (A : GL (Fin 2) ℝ) (hA : 0 < A.det.val) :
    IntegrableOn (petersson 2 f (g ∣[(2:ℤ)] A⁻¹)) (A • lpsGamma0PeterssonDomain N) volume := by sorry
