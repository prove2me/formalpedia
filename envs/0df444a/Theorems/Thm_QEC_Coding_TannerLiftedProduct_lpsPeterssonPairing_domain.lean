-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsPeterssonPairing_domain
-- name    : QEC.Coding.TannerLiftedProduct.lpsPeterssonPairing_domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:19:42.888177+00:00
-- url     : https://prove2.me/theorems/bd470c76-1894-494f-82ba-e2a3c7b684d9
-- title:
--   Tanner Lifted Product: lps Petersson Pairing domain
-- statement:
--   The original pairing equals its actual trace integral on every genuine effective modular domain.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L26-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L26-L30

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsPeterssonPairing_domain (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain lpsEffectiveModularGroup s volume) :
    lpsCuspPeterssonPairing N f g = ∫τ in s,lpsCuspPeterssonTrace N f g τ := by sorry
