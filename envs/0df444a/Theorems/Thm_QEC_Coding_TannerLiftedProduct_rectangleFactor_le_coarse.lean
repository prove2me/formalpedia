-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_rectangleFactor_le_coarse
-- name    : QEC.Coding.TannerLiftedProduct.rectangleFactor_le_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:45.417613+00:00
-- url     : https://prove2.me/theorems/c1f3f908-3004-4808-8483-072759abf5fe
-- title:
--   Tanner Lifted Product: rectangle Factor le coarse
-- statement:
--   The exact sparse-rectangle factor used by the bidirectional union bound
--   is bounded by `coarseRectangleFactor`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L296-L323
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L296-L323

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

theorem QEC.Coding.TannerLiftedProduct.rectangleFactor_le_coarse
    (w m s q : Nat) :
    (Nat.choose w (w - 2 * m)) ^ 2 *
        (s * (((w - 2 * m) * (w - 2 * m) + 1) ^ s) *
          q ^ (2 * (2 * m) * w + s)) ≤
      coarseRectangleFactor w m s q := by sorry
