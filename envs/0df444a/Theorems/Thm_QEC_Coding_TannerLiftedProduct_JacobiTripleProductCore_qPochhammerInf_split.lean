-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPochhammerInf_split
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPochhammerInf_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:04.190304+00:00
-- url     : https://prove2.me/theorems/ad03e388-a4df-42c2-9c9e-68d6c35d84e6
-- title:
--   Jacobi Triple Product Core: q Pochhammer Inf split
-- statement:
--   The Jacobi Triple Product Core construction uses the q Pochhammer Inf split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L938-L945
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L938-L945

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPochhammerInf_split (k : ℕ) : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) =
    qPoch (q ^ 2) (q ^ 2) k *
    qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) := by sorry
