-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lowWeightFactor_le_coarse
-- name    : QEC.Coding.TannerLiftedProduct.lowWeightFactor_le_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:18:26.441123+00:00
-- url     : https://prove2.me/theorems/b9524bfa-3feb-4125-baf5-d4a9cba12d86
-- title:
--   Tanner Lifted Product: low Weight Factor le coarse
-- statement:
--   The exact low-weight sum is bounded by `coarseLowWeightFactor`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L138-L143
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L138-L143

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

theorem QEC.Coding.TannerLiftedProduct.lowWeightFactor_le_coarse
    (w d q : Nat) (hq : 0 < q) :
    (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) ≤
      coarseLowWeightFactor w d q := by sorry
