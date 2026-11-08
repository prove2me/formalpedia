-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPeterssonPairing_translatedDomain
-- name    : QEC.Coding.TannerLiftedProduct.lpsPeterssonPairing_translatedDomain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:20:57.224973+00:00
-- url     : https://prove2.me/theorems/1f5179da-e91d-4a0a-b28c-b959d53d480a
-- title:
--   Tanner Lifted Product: lps Petersson Pairing translated Domain
-- statement:
--   Every actual translate of the proved modular domain computes the original pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L58-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L58-L62

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsPeterssonPairing_translatedDomain (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (h : lpsEffectiveModularGroup) :
    lpsCuspPeterssonPairing N f g = ∫τ in h • ModularGroup.fd,lpsCuspPeterssonTrace N f g τ := by sorry
