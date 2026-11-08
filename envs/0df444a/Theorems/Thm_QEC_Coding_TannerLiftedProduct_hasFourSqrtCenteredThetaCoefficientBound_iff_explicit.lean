-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasFourSqrtCenteredThetaCoefficientBound_iff_explicit
-- name    : QEC.Coding.TannerLiftedProduct.hasFourSqrtCenteredThetaCoefficientBound_iff_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:05:19.531106+00:00
-- url     : https://prove2.me/theorems/18e077e3-04d6-48f7-9265-bba5b6ca12fd
-- title:
--   Tanner Lifted Product: has Four Sqrt Centered Theta Coefficient Bound iff explicit
-- statement:
--   The relaxed hypothesis is an explicit estimate on the original theta
--   representation count after elementary trivial-mode subtraction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L396-L410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L396-L410

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.hasFourSqrtCenteredThetaCoefficientBound_iff_explicit
    (a : LPSResiduePrime p) :
    HasFourSqrtCenteredThetaCoefficientBound a ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |(Fintype.card PSL(2, ZMod a.q) : ℝ) *
              ((PowerSeries.coeff (p ^ (2 * n))
                (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
            2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
              (-(p : ℝ)) ^ n)| ≤
          C * (((2 * n + 1 : ℕ) : ℝ) * (4 * (p : ℝ)) ^ n) := by sorry
