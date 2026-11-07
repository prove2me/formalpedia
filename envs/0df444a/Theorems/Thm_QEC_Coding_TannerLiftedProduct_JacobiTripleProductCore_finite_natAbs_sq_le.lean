-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_natAbs_sq_le
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_natAbs_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:15.882727+00:00
-- url     : https://prove2.me/theorems/3a7370a2-6e2f-4b3d-8b8e-ea7b9a9acff7
-- title:
--   Jacobi Triple Product Core: finite nat Abs sq le
-- statement:
--   The Jacobi Triple Product Core construction uses the finite nat Abs sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1271-L1275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1271-L1275

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_natAbs_sq_le (d : ℕ) :
    {m : ℤ | m.natAbs ^ 2 ≤ d}.Finite := by sorry
