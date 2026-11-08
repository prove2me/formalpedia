-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasOptimalCenteredThetaCoefficientBound_iff_explicit
-- name    : QEC.Coding.TannerLiftedProduct.hasOptimalCenteredThetaCoefficientBound_iff_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:03:43.663564+00:00
-- url     : https://prove2.me/theorems/7158d771-c892-4e66-ba96-495fcb06a8d7
-- title:
--   Tanner Lifted Product: has Optimal Centered Theta Coefficient Bound iff explicit
-- statement:
--   Fully expanded form of the one remaining automorphic estimate.  This
--   equivalence prevents the named residual predicate from hiding any spectral
--   or Hecke-polynomial premise: its left-hand side is exactly the explicit
--   theta representation number after subtraction of the elementary trivial
--   term displayed on the right.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L378-L392
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSRamanujanTraceBridge.lean#L378-L392

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.hasOptimalCenteredThetaCoefficientBound_iff_explicit
    (a : LPSResiduePrime p) :
    HasOptimalCenteredThetaCoefficientBound a ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |(Fintype.card PSL(2, ZMod a.q) : ℝ) *
              ((PowerSeries.coeff (p ^ (2 * n))
                (lpsTraceThetaSeries a.q) : ℕ) : ℝ) -
            2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
              (-(p : ℝ)) ^ n)| ≤
          C * (((2 * n + 1 : ℕ) : ℝ) * (p : ℝ) ^ n) := by sorry
