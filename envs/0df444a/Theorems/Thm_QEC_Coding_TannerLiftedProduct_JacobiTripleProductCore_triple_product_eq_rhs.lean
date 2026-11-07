-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_triple_product_eq_rhs
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.triple_product_eq_rhs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:17:30.742541+00:00
-- url     : https://prove2.me/theorems/647bd243-e626-4ca3-8ba5-ec43de562c32
-- title:
--   Jacobi Triple Product Core: triple product eq rhs
-- statement:
--   The Jacobi Triple Product Core construction uses the triple product eq rhs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1946-L1952
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1946-L1952

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.triple_product_eq_rhs : letI := piTop;
    qPochhammerInf (q ^ 2) (q ^ 2) * qPochhammerInf (-q * a) (q ^ 2) *
    qPochhammerInf (-q * aI) (q ^ 2) = rhs := by sorry
