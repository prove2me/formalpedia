-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_hasSum_CS_mul_t_pow
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.hasSum_CS_mul_t_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:12:02.786732+00:00
-- url     : https://prove2.me/theorems/16c5bc38-ac1c-4e3a-b7da-c3b973a13c4a
-- title:
--   Jacobi Triple Product Core: has Sum CS mul t pow
-- statement:
--   The Jacobi Triple Product Core construction uses the has Sum CS mul t pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L618-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L618-L631

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.hasSum_CS_mul_t_pow (c : ℕ → R) :
    letI := piTopS
    HasSum (fun k => CS (c k) * t ^ k) (PowerSeries.mk c) := by sorry
