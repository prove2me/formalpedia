-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_sum_right
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_sum_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:00:28.484893+00:00
-- url     : https://prove2.me/theorems/ed97266e-ff4b-4922-9590-488e42afe0d3
-- title:
--   Tanner Lifted Product: lps Cusp Hecke Pairing sum right
-- statement:
--   The original right Hecke pairing is the true finite sum of convergent right-factor slash integrals.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L134-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L134-L148

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_sum_right (N p : ℕ) [NeZero N] [Fact p.Prime]
    (hNp : p.Coprime N)
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) :
    lpsCuspPeterssonPairing N f (lpsCuspHeckeLinearMap N p hNp g) =
      ∑i:Option (Fin p), ∫τ in lpsGamma0PeterssonDomain N,
        petersson 2 f (g ∣[(2:ℤ)] lpsHeckeUpperGL ℝ p i) τ := by sorry
