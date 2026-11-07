-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_restrict_Z_to_N
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.restrict_Z_to_N
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:25.938207+00:00
-- url     : https://prove2.me/theorems/245126a4-72de-44a5-90cf-093d49e782a6
-- title:
--   Jacobi Triple Product Core: restrict Z to N
-- statement:
--   The Jacobi Triple Product Core construction uses the restrict Z to N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1928-L1934
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1928-L1934

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.restrict_Z_to_N : letI := piTop;
    (∑' p : ℤ × ℕ, PowerSeries.C (LaurentPolynomial.T p.1) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + ↑p.2).natAbs ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) =
    (∑' p : ℕ × ℕ, PowerSeries.C (LaurentPolynomial.T (↑p.1)) *
      ((-1 : R) ^ p.2 * q ^ ((p.1 + p.2) ^ 2 + p.2)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1) := by sorry
