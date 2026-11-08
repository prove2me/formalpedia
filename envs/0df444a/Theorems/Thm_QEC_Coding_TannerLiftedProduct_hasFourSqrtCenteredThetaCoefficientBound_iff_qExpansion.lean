-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_hasFourSqrtCenteredThetaCoefficientBound_iff_qExpansion
-- name    : QEC.Coding.TannerLiftedProduct.hasFourSqrtCenteredThetaCoefficientBound_iff_qExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:06:20.671127+00:00
-- url     : https://prove2.me/theorems/33a022a8-e05a-4ab4-8a2b-c1063fe7a2b6
-- title:
--   Tanner Lifted Product: has Four Sqrt Centered Theta Coefficient Bound iff q Expansion
-- statement:
--   The precise remaining coefficient estimate, expressed entirely in the
--   analytic `qExpansion` API.  This equivalence supplies no bound by itself.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularTraceBridge.lean#L46-L58
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSModularTraceBridge.lean#L46-L58

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSAnalyticTheta
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSModularTraceBridge
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
variable {p : ℕ}

theorem QEC.Coding.TannerLiftedProduct.hasFourSqrtCenteredThetaCoefficientBound_iff_qExpansion
    (a : LPSResiduePrime p) :
    HasFourSqrtCenteredThetaCoefficientBound a ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
        |(Fintype.card PSL(2, ZMod a.q) : ℝ) *
              (PowerSeries.coeff (p ^ (2 * n))
                (UpperHalfPlane.qExpansion 1
                  (fun z : ℍ => lpsStandardTheta a.q z))).re -
            2 * ((∑ i ∈ Finset.range (2 * n + 1), (p : ℝ) ^ i) -
              (-(p : ℝ)) ^ n)| ≤
          C * (((2 * n + 1 : ℕ) : ℝ) * (4 * (p : ℝ)) ^ n) := by sorry
