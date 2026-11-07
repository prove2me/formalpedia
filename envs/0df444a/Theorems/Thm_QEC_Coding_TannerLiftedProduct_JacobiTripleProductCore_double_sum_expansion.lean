-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_double_sum_expansion
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.double_sum_expansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:46.562774+00:00
-- url     : https://prove2.me/theorems/bce88ed0-3886-487e-b069-9ee915554fe4
-- title:
--   Jacobi Triple Product Core: double sum expansion
-- statement:
--   The Jacobi Triple Product Core construction uses the double sum expansion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1208-L1217
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1208-L1217

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.double_sum_expansion : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2) =
    ∑' p : ℕ × ℕ,
      PowerSeries.C (LaurentPolynomial.T (p.1 : ℤ)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1 := by sorry
