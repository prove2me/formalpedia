-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_V_recurrence
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.V_recurrence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:25.988435+00:00
-- url     : https://prove2.me/theorems/de469f23-9838-43dc-abb2-386db75e45a4
-- title:
--   Jacobi Triple Product Core: V recurrence
-- statement:
--   The Jacobi Triple Product Core construction uses the V recurrence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1544-L1548
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1544-L1548

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.V_recurrence (ℓ : ℕ) :
    V ℓ = V (ℓ + 1) * (1 - Q₀ ^ (ℓ + 1)) := by sorry
