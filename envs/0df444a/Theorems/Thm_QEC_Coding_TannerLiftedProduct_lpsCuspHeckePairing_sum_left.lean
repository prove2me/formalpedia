-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_sum_left
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_sum_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:57:41.936861+00:00
-- url     : https://prove2.me/theorems/ff3e897c-3e20-4ff2-8917-ae131d6e1905
-- title:
--   Tanner Lifted Product: lps Cusp Hecke Pairing sum left
-- statement:
--   The original Hecke pairing is the true finite sum of absolutely convergent slash integrals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L83-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L83-L95

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_sum_left (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N (lpsCuspHeckeLinearMap N p hNp f) g =
      ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        petersson 2 (f ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) g τ := by sorry
