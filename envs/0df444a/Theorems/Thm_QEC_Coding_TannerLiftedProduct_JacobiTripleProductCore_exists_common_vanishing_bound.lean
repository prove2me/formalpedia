-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_exists_common_vanishing_bound
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exists_common_vanishing_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:25.723528+00:00
-- url     : https://prove2.me/theorems/bce9393d-9d1d-4e74-84a1-d69b0a32ea6b
-- title:
--   Jacobi Triple Product Core: exists common vanishing bound
-- statement:
--   The Jacobi Triple Product Core construction uses the exists common vanishing bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1682-L1692
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1682-L1692

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.exists_common_vanishing_bound {G_type : Type*} [AddCommGroup G_type]
    {t w u : ℕ → G_type}
    (ht : (Function.support t).Finite)
    (hw : (Function.support w).Finite)
    (hu : (Function.support u).Finite) :
    ∃ N, ∀ i, N < i → t i = 0 ∧ w i = 0 ∧ u i = 0 := by sorry
