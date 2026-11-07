-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_eval_B
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:45.708467+00:00
-- url     : https://prove2.me/theorems/321b6864-e7cb-4422-82e2-24957d85271a
-- title:
--   Jacobi Triple Product Core: eval B
-- statement:
--   The Jacobi Triple Product Core construction uses the eval B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L860-L877
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L860-L877

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.eval_B (x : R) (hx : x.constantCoeff = 0) : letI := piTop;
    eval_x_fun x B_S = qPochhammerInf (-x) (q ^ 2) := by sorry
