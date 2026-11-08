-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPeterssonTrace_effectiveInvariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsPeterssonTrace_effectiveInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:18:46.455407+00:00
-- url     : https://prove2.me/theorems/1a4aaa4f-ed5c-45d4-9b86-d9a707b7f6e0
-- title:
--   Tanner Lifted Product: lps Petersson Trace effective Invariant
-- statement:
--   The original actual finite-coset Petersson trace is invariant under the effective modular action.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L16-L23
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L16-L23

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsPeterssonTrace_effectiveInvariant (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) (τ : ℍ) :
    lpsCuspPeterssonTrace N f g (h • τ) = lpsCuspPeterssonTrace N f g τ := by sorry
