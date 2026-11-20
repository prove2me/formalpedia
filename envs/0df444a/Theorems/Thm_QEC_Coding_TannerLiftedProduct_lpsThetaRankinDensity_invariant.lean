-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsThetaRankinDensity_invariant
-- name    : QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:27:19.723597+00:00
-- url     : https://prove2.me/theorems/9967feaa-8b9d-4171-86de-95f334988d33
-- title:
--   Tanner Lifted Product: lps Theta Rankin Density invariant
-- statement:
--   The actual LPS theta square density is invariant under the whole modular group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L36-L40
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaRankinDensity.lean#L36-L40

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaRankinDensity
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Asymptotics Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ComplexConjugate
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsThetaRankinDensity_invariant (q : ℕ) [Fact q.Prime] (hq4 : q%4=1)
    (h : SL(2,ℤ)) (τ : ℍ) :
    lpsThetaRankinDensity q hq4 (h • τ)=lpsThetaRankinDensity q hq4 τ := by sorry
