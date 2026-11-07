-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_support_set
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_support_set
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:09:48.9392+00:00
-- url     : https://prove2.me/theorems/18123545-0768-458f-9dcc-066e4d61749a
-- title:
--   Jacobi Triple Product Core: finite support set
-- statement:
--   The Jacobi Triple Product Core construction uses the finite support set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1326-L1337
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1326-L1337

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_support_set (d : ℕ) :
    Set.Finite {p : ℤ × ℕ | p.1.natAbs ^ 2 + p.2 ≤ d} := by sorry
