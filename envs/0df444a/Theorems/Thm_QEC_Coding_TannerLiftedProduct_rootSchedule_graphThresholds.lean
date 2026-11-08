-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rootSchedule_graphThresholds
-- name    : QEC.Coding.TannerLiftedProduct.rootSchedule_graphThresholds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:09:25.813038+00:00
-- url     : https://prove2.me/theorems/68cedfad-e2f2-4df8-b836-5d1f65c57322
-- title:
--   Tanner Lifted Product: root Schedule graph Thresholds
-- statement:
--   Graph thresholds for a replicated local length `A N`, where
--   `x^6 ≤ N ≤ 64 x^6`.  The upper bound controls the logarithmic face term;
--   the lower bound supplies the distance scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L670-L751
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L670-L751

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

theorem QEC.Coding.TannerLiftedProduct.rootSchedule_graphThresholds
    (A D M S C N x : Nat) (lambda : ℝ) (hx : 0 < x)
    (hLower : x ^ 6 ≤ N) (hUpper : N ≤ 64 * x ^ 6)
    (hLambdaNonnegative : 0 ≤ lambda)
    (hLambda : lambda ≤ ((C * x ^ 3 : Nat) : ℝ))
    (hVertical : 2 * M + C ≤ D * x ^ 2)
    (hEdge : 4 * C ≤ M * x)
    (hFace : 16 * (128 * A + 6 * x + 1) * C ^ 2 ≤ S * x) :
    ((2 * (M * x ^ 4) : Nat) : ℝ) + lambda ≤ (D * N : Nat) ∧
    2 * (2 * lambda) ≤ ((M * x ^ 4 : Nat) : ℝ) ∧
    2 * (((Nat.log 2 (2 * (A * N)) + 1 : Nat) : ℝ) *
      (8 * lambda ^ 2)) ≤ ((S * x ^ 7 : Nat) : ℝ) := by sorry
