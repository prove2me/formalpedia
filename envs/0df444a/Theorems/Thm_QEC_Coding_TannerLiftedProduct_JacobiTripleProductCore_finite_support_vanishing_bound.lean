-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_finite_support_vanishing_bound
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_support_vanishing_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:29.712721+00:00
-- url     : https://prove2.me/theorems/3c739835-8f18-469c-98b2-57bedc2e55d1
-- title:
--   Jacobi Triple Product Core: finite support vanishing bound
-- statement:
--   The Jacobi Triple Product Core construction uses the finite support vanishing bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1676-L1680
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1676-L1680

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.finite_support_vanishing_bound {G_type : Type*} [AddCommGroup G_type]
    {f : ℕ → G_type} (hf : (Function.support f).Finite) :
    ∃ N, ∀ i, N < i → f i = 0 := by sorry
