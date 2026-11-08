-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_weightedBlockFactor_lt_of_logarithmicRows
-- name    : QEC.Coding.TannerLiftedProduct.weightedBlockFactor_lt_of_logarithmicRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:51:22.797369+00:00
-- url     : https://prove2.me/theorems/20f7f33c-43e4-441a-99b7-55cbd47e33ec
-- title:
--   Tanner Lifted Product: weighted Block Factor lt of logarithmic Rows
-- statement:
--   The quadratic weight turns the one-block low-weight event into a pure
--   logarithmic row budget.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L39-L112
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L39-L112

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduledLocalPair
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_24
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_ffaee19b85_25

theorem QEC.Coding.TannerLiftedProduct.weightedBlockFactor_lt_of_logarithmicRows
    (q A D r : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hD : D ≤ A)
    (hRows : logarithmicLocalRows q A D ≤ r) :
    6 * (q + quadraticWeightBase q A) ^ A <
      q ^ r * (quadraticWeightBase q A) ^ (A - D) := by sorry
