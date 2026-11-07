-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_x_one
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:43.639195+00:00
-- url     : https://prove2.me/theorems/043ec450-44bb-4b6a-a9a9-8229b317effc
-- title:
--   Jacobi Triple Product Core: eval x one
-- statement:
--   The Jacobi Triple Product Core construction uses the eval x one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L830-L835
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L830-L835

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_x_one (x : R) (_hx : x.constantCoeff = 0) :
    eval_x_fun x 1 = 1 := by sorry
