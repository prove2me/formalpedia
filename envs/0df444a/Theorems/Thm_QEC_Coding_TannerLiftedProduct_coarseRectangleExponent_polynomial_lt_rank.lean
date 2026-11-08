-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_polynomial_lt_rank
-- name    : QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_polynomial_lt_rank
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:32.502971+00:00
-- url     : https://prove2.me/theorems/60a19337-6239-441e-b3de-a5bf051e62f5
-- title:
--   Tanner Lifted Product: coarse Rectangle Exponent polynomial lt rank
-- statement:
--   A linear threshold on `n` makes the polynomial rectangle exponent
--   strictly smaller than the PK22 rank budget `k r = n^5 * (B n^6)`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L228-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L228-L239

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

theorem QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_polynomial_lt_rank
    (A B n q : Nat) (hq : 2 ≤ q) (hA : 0 < A) (hn : 0 < n)
    (hThreshold : 8 * A + 26 < B * n) :
    coarseRectangleExponent (A * n ^ 6) (n ^ 4) (n ^ 7) q + 3 <
      n ^ 5 * (B * n ^ 6) := by sorry
