-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredThetaResidual_even_eq_qExpansion_sub_explicit
-- name    : QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_qExpansion_sub_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:55:57.021639+00:00
-- url     : https://prove2.me/theorems/8dff8fe3-b8fb-4726-b634-37e46501b20d
-- title:
--   Tanner Lifted Product: lps Centered Theta Residual even eq q Expansion sub explicit
-- statement:
--   Exact analytic-coefficient form of the centered LPS residual at even
--   Hecke degree.  The real part is explicit because the theta coefficients
--   are natural numbers.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularTraceBridge.lean#L23-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularTraceBridge.lean#L23-L42

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_qExpansion_sub_explicit
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2 * n) =
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
        (PowerSeries.coeff (p ^ (2 * n))
          (UpperHalfPlane.qExpansion 1
            (fun z : ℍ => lpsStandardTheta a.q z))).re -
        2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
          (-(p : ℝ)) ^ n) := by sorry
