-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_rootSchedule_coeff_lt_rank
-- name    : QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_rootSchedule_coeff_lt_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:17.937915+00:00
-- url     : https://prove2.me/theorems/e771d0dc-9a9b-4a8a-9250-7c2985d6b524
-- title:
--   Tanner Lifted Product: coarse Rectangle Exponent root Schedule coeff lt rank
-- statement:
--   Rectangle/rank comparison for an arbitrary block quotient `N`.  If
--   `x^6 ≤ N ≤ 64 x^6`, the existing polynomial estimate applies after widening
--   the local length from `A N` to `(64 A) x^6`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L261-L298
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L261-L298

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerSemanticDistance
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerScheduleBounds
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {F G W R R' : Type u}
variable [Field F] [Fintype F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_23
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_5f18e3d3db_24

theorem QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_rootSchedule_coeff_lt_rank
    (A M S K B N x q : Nat)
    (hq : 2 ≤ q) (hA : 0 < A) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hThreshold :
      2 * (64 * A) + 2 * (64 * A) * S + 4 * M * (64 * A) +
          16 * S + 11 < K * B * x) :
    coarseRectangleExponent (A * N) (M * x ^ 4) (S * x ^ 7) q + 3 <
      (K * x ^ 5) * (B * N) := by sorry
