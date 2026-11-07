-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_V_coeff_neg_eq_zero
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.V_coeff_neg_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:10:05.816992+00:00
-- url     : https://prove2.me/theorems/36c7fba5-aa29-47ac-bb8b-0fba62bc4b01
-- title:
--   Jacobi Triple Product Core: V coeff neg eq zero
-- statement:
--   The Jacobi Triple Product Core construction uses the V coeff neg eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1576-L1579
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1576-L1579

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.V_coeff_neg_eq_zero (ℓ : ℕ) (d : ℤ) (hd : d < 0) :
    (V ℓ).coeff d = 0 := by sorry
