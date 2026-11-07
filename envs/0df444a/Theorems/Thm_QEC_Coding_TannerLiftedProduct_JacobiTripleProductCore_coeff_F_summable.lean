-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_F_summable
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_F_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:07.37125+00:00
-- url     : https://prove2.me/theorems/55c9d1df-ce1e-412c-97da-57287657b6e7
-- title:
--   Jacobi Triple Product Core: coeff F summable
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff F summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1854-L1858
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1854-L1858

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_F_summable (d : ℕ) : letI := piTop;
    Summable (fun (p : ℤ × ℕ) => (PowerSeries.coeff d) (F p)) := by sorry
