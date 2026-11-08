-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_polynomialSchedule_graphThresholds
-- name    : QEC.Coding.TannerLiftedProduct.polynomialSchedule_graphThresholds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T12:08:56.52949+00:00
-- url     : https://prove2.me/theorems/cd7566a9-6479-4803-b7d4-ee5353b374e0
-- title:
--   Tanner Lifted Product: polynomial Schedule graph Thresholds
-- statement:
--   A spectral scale `lambda ≤ C n^3` implies the three deterministic graph
--   thresholds for the coefficient-bearing polynomial schedule, subject only to
--   finite coefficient inequalities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L593-L665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L593-L665

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

theorem QEC.Coding.TannerLiftedProduct.polynomialSchedule_graphThresholds
    (A D M S C n : Nat) (lambda : ℝ) (hn : 0 < n)
    (hLambdaNonnegative : 0 ≤ lambda)
    (hLambda : lambda ≤ ((C * n ^ 3 : Nat) : ℝ))
    (hVertical : 2 * M + C ≤ D * n ^ 2)
    (hEdge : 4 * C ≤ M * n)
    (hFace : 16 * (2 * A + 6 * n + 1) * C ^ 2 ≤ S * n) :
    ((2 * (M * n ^ 4) : Nat) : ℝ) + lambda ≤ (D * n ^ 6 : Nat) ∧
    2 * (2 * lambda) ≤ ((M * n ^ 4 : Nat) : ℝ) ∧
    2 * (((Nat.log 2 (2 * (A * n ^ 6)) + 1 : Nat) : ℝ) *
      (8 * lambda ^ 2)) ≤ ((S * n ^ 7 : Nat) : ℝ) := by sorry
