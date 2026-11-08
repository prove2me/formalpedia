-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_polynomialSchedule_sizeBounds
-- name    : QEC.Coding.TannerLiftedProduct.polynomialSchedule_sizeBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:51:22.04635+00:00
-- url     : https://prove2.me/theorems/8fcf3ac4-0a16-44e9-8124-218acbb5fbea
-- title:
--   Tanner Lifted Product: polynomial Schedule size Bounds
-- statement:
--   The elementary size conditions required by the deterministic and random
--   local-code theorems for the polynomial schedule reduce to three small
--   coefficient inequalities.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L303-L346
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L303-L346

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

theorem QEC.Coding.TannerLiftedProduct.polynomialSchedule_sizeBounds
    (A D n : Nat) (hD : D ≤ A) (hDPositive : 0 < D) (hn : 0 < n)
    (hSmall : 12 ≤ D * n ^ 2)
    (hRank : 36 ≤ 5 * D ^ 2)
    (hRectangle : 4 ≤ D * n ^ 3) :
    0 < D * n ^ 6 ∧
    D * n ^ 6 ≤ A * n ^ 6 ∧
    6 * (2 * n ^ 4) ≤ D * n ^ 6 ∧
    36 * n ^ 5 * n ^ 7 ≤ 5 * (D * n ^ 6) * (D * n ^ 6) ∧
    4 ≤ D * n ^ 6 ∧
    4 * n ^ 4 ≤ D * n ^ 6 ∧
    4 * n ^ 7 ≤ n ^ 4 * (D * n ^ 6) := by sorry
