-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPochhammerInf_eq_tprod
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPochhammerInf_eq_tprod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:55.130319+00:00
-- url     : https://prove2.me/theorems/c159719d-b36f-4829-865e-869186ec1e29
-- title:
--   Jacobi Triple Product Core: q Pochhammer Inf eq tprod
-- statement:
--   The Jacobi Triple Product Core construction uses the q Pochhammer Inf eq tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L239-L244
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L239-L244

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPochhammerInf_eq_tprod (a Q : R)
    (hm : letI := piTop; Multipliable (fun n ↦ 1 - a * Q ^ n)) : letI := piTop;
    qPochhammerInf a Q = ∏' n, (1 - a * Q ^ n) := by sorry
