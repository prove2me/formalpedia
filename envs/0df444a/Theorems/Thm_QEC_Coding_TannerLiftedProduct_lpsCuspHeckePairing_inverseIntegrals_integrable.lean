-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCuspHeckePairing_inverseIntegrals_integrable
-- name    : QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_inverseIntegrals_integrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:06:13.971586+00:00
-- url     : https://prove2.me/theorems/b7f5df1c-89bc-4bd5-aa6f-9fbf0f61c66a
-- title:
--   Tanner Lifted Product: lps Cusp Hecke Pairing inverse Integrals integrable
-- statement:
--   Every transferred genuine determinant-p Hecke integral is absolutely convergent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L112-L119
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSHeckePeterssonIntegrals.lean#L112-L119

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSGamma0PeterssonDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCoefficients
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsCuspHeckePairing_inverseIntegrals_integrable (N p : ℕ) [NeZero N] [Fact p.Prime]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2)
    (i : Option (Fin p)) :
    IntegrableOn (petersson 2 f (g ∣[(2:ℤ)] (lpsHeckeUpperGL ℝ p i)⁻¹))
      ((lpsHeckeUpperGL ℝ p i) • lpsGamma0PeterssonDomain N) volume := by sorry
