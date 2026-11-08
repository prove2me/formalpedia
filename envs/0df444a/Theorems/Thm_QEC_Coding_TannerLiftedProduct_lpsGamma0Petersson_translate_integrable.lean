-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Petersson_translate_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_translate_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:53:29.736226+00:00
-- url     : https://prove2.me/theorems/2c8ee060-5c80-4089-8d4b-555a727785b4
-- title:
--   Tanner Lifted Product: lps Gamma0 Petersson translate integrable
-- statement:
--   The genuine cusp bound gives absolute convergence on every actual modular translate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L45-L56
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L45-L56

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_translate_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) :
    IntegrableOn (petersson 2 f g) (h • ModularGroup.fd) volume := by sorry
