-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsGamma0Petersson_effectiveInvariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_effectiveInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:53:39.738501+00:00
-- url     : https://prove2.me/theorems/42bcf5c6-80ef-48fa-abd9-7633b59a948d
-- title:
--   Tanner Lifted Product: lps Gamma0 Petersson effective Invariant
-- statement:
--   The genuine Petersson integrand is invariant under the actual effective Gamma0 action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L102-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L102-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsGamma0Petersson_effectiveInvariant (N : ℕ)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveGamma0 N) (τ : ℍ) :
    petersson 2 f g (h • τ) = petersson 2 f g τ := by sorry
