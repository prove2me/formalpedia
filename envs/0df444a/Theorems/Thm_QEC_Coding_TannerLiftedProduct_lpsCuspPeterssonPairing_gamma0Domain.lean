-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspPeterssonPairing_gamma0Domain
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_gamma0Domain
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:54:42.116649+00:00
-- url     : https://prove2.me/theorems/fd84121c-a29a-4aa3-a7b7-4a1f7656a7e5
-- title:
--   Tanner Lifted Product: lps Cusp Petersson Pairing gamma0 Domain
-- statement:
--   Every actual effective Gamma0 fundamental domain computes the original untraced pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L121-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSGamma0PeterssonDomain.lean#L121-L126

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCosetSectionDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonPositive
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspPeterssonPairing_gamma0Domain (N : ℕ) [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    {s : Set ℍ} (hs : IsFundamentalDomain (lpsEffectiveGamma0 N) s volume) :
    lpsCuspPeterssonPairing N f g = ∫τ in s,petersson 2 f g τ := by sorry
