-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_x_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:43.593382+00:00
-- url     : https://prove2.me/theorems/8540a359-28ab-408c-86c2-4cc7dd16d951
-- title:
--   Jacobi Triple Product Core: eval x mul
-- statement:
--   The Jacobi Triple Product Core construction uses the eval x mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L810-L828
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L810-L828

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_mul (x : R) (hx : x.constantCoeff = 0) (p q : S) :
    eval_x_fun x (p * q) = eval_x_fun x p * eval_x_fun x q := by sorry
