-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0PeterssonDomain_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:33.507817+00:00
-- url     : https://prove2.me/theorems/1b8c5c6c-6969-4dab-b674-610e99c54583
-- title:
--   Tanner Lifted Product: lps Gamma0 Petersson Domain integrable
-- statement:
--   The original finite-cover Gamma0 Petersson integral is absolutely convergent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L112-L118
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L112-L118

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0PeterssonDomain_integrable (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    IntegrableOn (petersson 2 f g) (lpsGamma0PeterssonDomain N) volume := by sorry
