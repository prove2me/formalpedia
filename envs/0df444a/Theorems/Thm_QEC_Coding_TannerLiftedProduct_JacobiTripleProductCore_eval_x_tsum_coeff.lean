-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_x_tsum_coeff
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_tsum_coeff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:26.61719+00:00
-- url     : https://prove2.me/theorems/9af8a1ac-0038-4458-b216-90d9266c99fa
-- title:
--   Jacobi Triple Product Core: eval x tsum coeff
-- statement:
--   The Jacobi Triple Product Core construction uses the eval x tsum coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L837-L845
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L837-L845

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_tsum_coeff (x : R) (_hx : x.constantCoeff = 0) (c : ℕ → R) :
    eval_x_fun x (letI := piTopS; ∑' n, CS (c n) * t ^ n) =
    (letI := piTop; ∑' n, c n * x ^ n) := by sorry
