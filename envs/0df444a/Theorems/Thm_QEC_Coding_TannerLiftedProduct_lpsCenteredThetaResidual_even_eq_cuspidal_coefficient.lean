-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredThetaResidual_even_eq_cuspidal_coefficient
-- name    : QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_cuspidal_coefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T07:23:12.789549+00:00
-- url     : https://prove2.me/theorems/39268942-466c-4c21-8f3a-18f5667feea0
-- title:
--   Tanner Lifted Product: lps Centered Theta Residual even eq cuspidal coefficient
-- statement:
--   Identify the exact centered trace with the genuine cusp coefficient and the retained signed term.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L202-L232
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaCuspidalRemainder.lean#L202-L232

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspFactorization
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaModularForm
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm

theorem QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_cuspidal_coefficient (p : ℕ)
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2*n)=
      (Fintype.card PSL(2,ZMod a.q):ℝ)*
        (PowerSeries.coeff (p^(2*n)) (UpperHalfPlane.qExpansion 1
          (lpsThetaCuspidalRemainder a.q a.modFour))).re+2*(-(p:ℝ))^n := by sorry
