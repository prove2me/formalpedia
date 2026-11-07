-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_rhs_terms
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_rhs_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:14.172103+00:00
-- url     : https://prove2.me/theorems/a2486fa0-178a-4617-9729-bbd854b1435d
-- title:
--   Jacobi Triple Product Core: summable rhs terms
-- statement:
--   The Jacobi Triple Product Core construction uses the summable rhs terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1286-L1290
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1286-L1290

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_rhs_terms : letI := piTop;
    Summable (fun m : ℤ => PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) := by sorry
