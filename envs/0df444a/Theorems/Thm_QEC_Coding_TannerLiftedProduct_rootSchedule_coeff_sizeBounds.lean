-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rootSchedule_coeff_sizeBounds
-- name    : QEC.Coding.TannerLiftedProduct.rootSchedule_coeff_sizeBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:52:00.889447+00:00
-- url     : https://prove2.me/theorems/c374f37d-484f-4008-8d54-2e034ea8f800
-- title:
--   Tanner Lifted Product: root Schedule coeff size Bounds
-- statement:
--   Deterministic size bounds when the replicated local length is an
--   arbitrary quotient `N` lying between `x^6` and `64 x^6`.  The auxiliary
--   PK22 scales remain `m = M x^4`, `s = S x^7`, and `k = K x^5`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L405-L463
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L405-L463

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

theorem QEC.Coding.TannerLiftedProduct.rootSchedule_coeff_sizeBounds
    (A D M S K N x : Nat)
    (hD : D ≤ A) (hDPositive : 0 < D) (hMPositive : 0 < M)
    (hx : 0 < x) (hLower : x ^ 6 ≤ N)
    (hSmall : 12 * M ≤ D * x ^ 2)
    (hRank : 36 * K * S ≤ 5 * D ^ 2)
    (hRectangle : 4 * S ≤ M * D * x ^ 3) :
    0 < D * N ∧
    D * N ≤ A * N ∧
    6 * (2 * (M * x ^ 4)) ≤ D * N ∧
    36 * (K * x ^ 5) * (S * x ^ 7) ≤ 5 * (D * N) * (D * N) ∧
    4 ≤ D * N ∧
    4 * (M * x ^ 4) ≤ D * N ∧
    4 * (S * x ^ 7) ≤ (M * x ^ 4) * (D * N) := by sorry
