-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_coarseRectangleExponent_mono_width
-- name    : QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_mono_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:48:41.680316+00:00
-- url     : https://prove2.me/theorems/088bfcdc-84b0-46f1-b4e1-c240ee35f994
-- title:
--   Tanner Lifted Product: coarse Rectangle Exponent mono width
-- statement:
--   The coarse sparse-rectangle exponent is monotone in the local-code
--   width.  This lets an arbitrary block quotient be rounded up to the next
--   controlled sixth-power scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L132-L140
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduleBounds.lean#L132-L140

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

theorem QEC.Coding.TannerLiftedProduct.coarseRectangleExponent_mono_width
    (w w' m s q : Nat) (hWidth : w ≤ w') :
    coarseRectangleExponent w m s q ≤
      coarseRectangleExponent w' m s q := by sorry
