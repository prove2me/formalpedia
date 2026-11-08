-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_replicate_scaled_add_pow_budget
-- name    : QEC.Coding.TannerLiftedProduct.replicate_scaled_add_pow_budget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:20.521021+00:00
-- url     : https://prove2.me/theorems/d876e216-9407-403b-b03c-ac34c0838970
-- title:
--   Tanner Lifted Product: replicate scaled add pow budget
-- statement:
--   A strict weighted-binomial budget on one parameter block replicates on
--   every positive multiple of that block.  Including the constant `6` in the
--   one-block hypothesis absorbs the six bad events without an asymptotic
--   constant argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L200-L217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L200-L217

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

theorem QEC.Coding.TannerLiftedProduct.replicate_scaled_add_pow_budget
    (A D B q L n : Nat) (hn : 0 < n)
    (hBlock : 6 * (q + L) ^ A < q ^ B * L ^ (A - D)) :
    6 * (q + L) ^ (A * n) <
      q ^ (B * n) * L ^ (A * n - D * n) := by sorry
