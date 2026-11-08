-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_polynomialSchedule_coeff_sizeBounds
-- name    : QEC.Coding.TannerLiftedProduct.polynomialSchedule_coeff_sizeBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:51:29.836405+00:00
-- url     : https://prove2.me/theorems/a5786b8c-03fa-45d8-a10e-3c1136a33d45
-- title:
--   Tanner Lifted Product: polynomial Schedule coeff size Bounds
-- statement:
--   Coefficient-bearing deterministic size bounds for
--   `m = M n^4`, `s = S n^7`, and `k = K n^5`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L350-L400
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L350-L400

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

theorem QEC.Coding.TannerLiftedProduct.polynomialSchedule_coeff_sizeBounds
    (A D M S K n : Nat)
    (hD : D ≤ A) (hDPositive : 0 < D) (hMPositive : 0 < M) (hn : 0 < n)
    (hSmall : 12 * M ≤ D * n ^ 2)
    (hRank : 36 * K * S ≤ 5 * D ^ 2)
    (hRectangle : 4 * S ≤ M * D * n ^ 3) :
    0 < D * n ^ 6 ∧
    D * n ^ 6 ≤ A * n ^ 6 ∧
    6 * (2 * (M * n ^ 4)) ≤ D * n ^ 6 ∧
    36 * (K * n ^ 5) * (S * n ^ 7) ≤
      5 * (D * n ^ 6) * (D * n ^ 6) ∧
    4 ≤ D * n ^ 6 ∧
    4 * (M * n ^ 4) ≤ D * n ^ 6 ∧
    4 * (S * n ^ 7) ≤ (M * n ^ 4) * (D * n ^ 6) := by sorry
