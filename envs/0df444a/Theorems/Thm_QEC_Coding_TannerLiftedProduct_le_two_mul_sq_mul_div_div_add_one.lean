-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_le_two_mul_sq_mul_div_div_add_one
-- name    : QEC.Coding.TannerLiftedProduct.le_two_mul_sq_mul_div_div_add_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:29:35.932805+00:00
-- url     : https://prove2.me/theorems/240929ce-a36d-4451-8d31-1f99710ae972
-- title:
--   Tanner Lifted Product: le two mul sq mul div div add one
-- statement:
--   Two successive positive-denominator divisions lose at most the displayed
--   factor.  This is the integer rounding lemma behind the canonical relative
--   distance.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L57-L82
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/TannerFamily.lean#L57-L82

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerPairExistence
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerFamily
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u
variable {A F W R R' : Type u} {G : A → Type u}
variable [Field F] [Fintype F]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
variable [∀ a, Group (G a)] [∀ a, Fintype (G a)]
variable [∀ a, DecidableEq (G a)]
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_34
attribute [local instance] QEC.Coding.TannerLiftedProduct._p2m_local_instance_4063ed27f1_35

theorem QEC.Coding.TannerLiftedProduct.le_two_mul_sq_mul_div_div_add_one
    (n w : Nat) (hw : 0 < w) :
    n ≤ 2 * w * w * (n / w / (2 * w) + 1) := by sorry
