-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_lowWeightFactor_lt_of_scaled_add_pow
-- name    : QEC.Coding.TannerLiftedProduct.lowWeightFactor_lt_of_scaled_add_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:50:21.294255+00:00
-- url     : https://prove2.me/theorems/ad1c517e-af7c-4d59-a049-b1fc515c7c75
-- title:
--   Tanner Lifted Product: low Weight Factor lt of scaled add pow
-- statement:
--   A scaled power budget implies the corresponding exact truncated-binomial
--   budget.  This is the cancellation form used by the four kernel/image bad
--   events in the random local-pair argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L184-L194
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerScheduledLocalPair.lean#L184-L194

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

theorem QEC.Coding.TannerLiftedProduct.lowWeightFactor_lt_of_scaled_add_pow
    (w d q L C target : Nat) (hd : d ≤ w) (hL : 0 < L)
    (hBudget : C * (q + L) ^ w < target * L ^ (w - d)) :
    C * (∑ t : Fin d, Nat.choose w t.1 * q ^ t.1) < target := by sorry
