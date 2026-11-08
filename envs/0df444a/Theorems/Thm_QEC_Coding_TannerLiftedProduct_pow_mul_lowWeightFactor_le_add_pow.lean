-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_pow_mul_lowWeightFactor_le_add_pow
-- name    : QEC.Coding.TannerLiftedProduct.pow_mul_lowWeightFactor_le_add_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:03.076729+00:00
-- url     : https://prove2.me/theorems/9c60f534-2839-41a0-8e86-dba7710fa7a6
-- title:
--   Tanner Lifted Product: pow mul low Weight Factor le add pow
-- statement:
--   A weighted binomial bound for the same low-weight sum.  Unlike
--   `lowWeightFactor_le_coarse`, this estimate remains exponential-linear when
--   `d` is a fixed fraction of `w`: multiplying the truncated sum by
--   `L^(w-d)` embeds every summand into the full expansion of `(q + L)^w`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L149-L179
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L149-L179

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

theorem QEC.Coding.TannerLiftedProduct.pow_mul_lowWeightFactor_le_add_pow
    (w d q L : Nat) (hd : d ≤ w) (hL : 0 < L) :
    L ^ (w - d) * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) ≤
      (q + L) ^ w := by sorry
