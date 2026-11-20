-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasFourSqrtCenteredThetaCoefficientBound_iff_cuspidal_coefficient
-- name    : QEC.Coding.TannerLiftedProduct.hasFourSqrtCenteredThetaCoefficientBound_iff_cuspidal_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:25:06.586771+00:00
-- url     : https://prove2.me/theorems/43e0ab9f-93e1-4a53-9590-91bd3b9e4180
-- title:
--   Tanner Lifted Product: has Four Sqrt Centered Theta Coefficient Bound iff cuspidal coefficient
-- statement:
--   Transport the remaining trace bound to the actual cuspidal coefficient without assuming that bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L235-L243
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L235-L243

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.hasFourSqrtCenteredThetaCoefficientBound_iff_cuspidal_coefficient (p : ℕ)
    (a : LPSResiduePrime p) :
    HasFourSqrtCenteredThetaCoefficientBound a ↔ ∃ C : ℝ,0≤C ∧ ∀ n : ℕ,
      |(Fintype.card PSL(2,ZMod a.q):ℝ)*
        (PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
          (lpsThetaCuspidalRemainder a.q a.modFour))).re+2*(-(p:ℝ))^n|≤
        C*(((2*n+1:ℕ):ℝ)*(4*(p:ℝ))^n) := by sorry
