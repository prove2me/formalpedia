-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_qPoch_split
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:08:53.196223+00:00
-- url     : https://prove2.me/theorems/41b2fc67-6b28-45af-aa37-1f0bb9fd75d2
-- title:
--   Jacobi Triple Product Core: q Poch split
-- statement:
--   The Jacobi Triple Product Core construction uses the q Poch split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L246-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L246-L249

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.qPoch_split (A Q : R) (n k : ℕ) :
    qPoch A Q (n + k) = qPoch A Q n * qPoch (A * Q ^ n) Q k := by sorry
