-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tail_factor_delta
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_factor_delta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:06.229222+00:00
-- url     : https://prove2.me/theorems/f4a7a2e2-a42e-4108-afbc-22ac467e09dd
-- title:
--   Jacobi Triple Product Core: tail factor delta
-- statement:
--   The Jacobi Triple Product Core construction uses the tail factor delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L269-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L269-L274

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tail_factor_delta (x : R) (m n : ℕ) (hmn : m < n) (i : ℕ)
    (j : ℕ) (hj : j ≤ m) :
    ((1 - ((-x * q) * (q ^ 2) ^ n) * (q ^ 2) ^ i : R)).coeff j =
    if j = 0 then 1 else 0 := by sorry
