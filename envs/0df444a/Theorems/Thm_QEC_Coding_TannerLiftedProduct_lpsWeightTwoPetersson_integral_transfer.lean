-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsWeightTwoPetersson_integral_transfer
-- name    : QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_integral_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:20:50.197477+00:00
-- url     : https://prove2.me/theorems/9ccdd367-9a08-442d-b692-8d5da0e92327
-- title:
--   Tanner Lifted Product: lps Weight Two Petersson integral transfer
-- statement:
--   The actual hyperbolic change of variables integrates the one-factor slash transfer.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L49-L55
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSPeterssonDomainTransfer.lean#L49-L55

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularFundamentalDomain
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspPeterssonTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSPeterssonDomainTransfer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section

theorem QEC.Coding.TannerLiftedProduct.lpsWeightTwoPetersson_integral_transfer (f g : ℍ → ℂ) (A : GL (Fin 2) ℝ)
    (hA : 0 < A.det.val) (s : Set ℍ) :
    (∫τ in s,petersson 2 (f ∣[(2 : ℤ)] A) g τ) =
      ∫τ in A • s,petersson 2 f (g ∣[(2 : ℤ)] A⁻¹) τ := by sorry
