-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qbinom_sum_rewrite
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qbinom_sum_rewrite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:11:28.019163+00:00
-- url     : https://prove2.me/theorems/5a0f279e-c3a3-41e2-ac21-9d8cb1e1d112
-- title:
--   Jacobi Triple Product Core: qbinom sum rewrite
-- statement:
--   The Jacobi Triple Product Core construction uses the qbinom sum rewrite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L340-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L340-L347

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qbinom_sum_rewrite (x : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (-(-x * q)) ^ k * (q ^ 2) ^ k.choose 2 =
    ∑ k ∈ Finset.range (n + 1),
      qBinom (q ^ 2) n k * (q ^ (k ^ 2) * x ^ k) := by sorry
