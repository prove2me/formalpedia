-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_inv_product_eq_qBinom_mul_inv
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.inv_product_eq_qBinom_mul_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:13.94502+00:00
-- url     : https://prove2.me/theorems/e75de788-9864-4eea-9364-cb4b3002878d
-- title:
--   Jacobi Triple Product Core: inv product eq q Binom mul inv
-- statement:
--   The Jacobi Triple Product Core construction uses the inv product eq q Binom mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L647-L664
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L647-L664

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.inv_product_eq_qBinom_mul_inv {n k : ℕ} (hkn : k ≤ n) :
    PowerSeries.invOfUnit (P (n - k)) 1 * PowerSeries.invOfUnit (P k) 1 =
    qBinom (q ^ 2) n k * PowerSeries.invOfUnit (P n) 1 := by sorry
