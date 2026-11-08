-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsCenteredThetaResidual_even_eq_theta_sub_explicit
-- name    : QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_theta_sub_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T11:52:37.659857+00:00
-- url     : https://prove2.me/theorems/f2f93464-c8e9-4b71-9d11-8cadeb91aa95
-- title:
--   Tanner Lifted Product: lps Centered Theta Residual even eq theta sub explicit
-- statement:
--   At even Hecke degree, the centered theta residual is the raw trace-theta
--   coefficient minus a completely explicit elementary term.  In particular,
--   the automorphic coefficient problem no longer contains an unevaluated Hecke
--   polynomial at zero.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L262-L270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L262-L270

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.lpsCenteredThetaResidual_even_eq_theta_sub_explicit
    (a : LPSResiduePrime p) (n : ℕ) :
    lpsCenteredThetaResidual a (2 * n) =
      (Fintype.card PSL(2, ZMod a.q) : ℝ) *
          ((PowerSeries.coeff (p ^ (2 * n))
            (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
        2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
          (-(p : ℝ)) ^ n) := by sorry
