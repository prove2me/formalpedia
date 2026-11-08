-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_inverseIntegrals
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_inverseIntegrals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:05:43.283263+00:00
-- url     : https://prove2.me/theorems/733d5e4f-5f7f-4ca9-9e53-e4fab8fad99e
-- title:
--   Tanner Lifted Product: lps Cusp Hecke Pairing inverse Integrals
-- statement:
--   Change of variables transfers the original Hecke pairing to actual inverse-matrix image integrals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L98-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L98-L109

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_inverseIntegrals (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∑i:Option (Fin p), ∫τ in (lpsHeckeUpperGL ℝ p i) • lpsGamma0PeterssonDomain N,
        petersson 2 f (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p i)⁻¹) τ := by sorry
