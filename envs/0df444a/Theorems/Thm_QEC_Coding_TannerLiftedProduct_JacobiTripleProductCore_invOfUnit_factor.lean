-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_invOfUnit_factor
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.invOfUnit_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:29.321562+00:00
-- url     : https://prove2.me/theorems/521f59e9-f0a9-4f9b-bb0d-9dab254acd65
-- title:
--   Jacobi Triple Product Core: inv Of Unit factor
-- statement:
--   The Jacobi Triple Product Core construction uses the inv Of Unit factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1523-L1533
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1523-L1533

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.invOfUnit_factor (ℓ : ℕ) :
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 =
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) (ℓ + 1)) 1 *
      (1 - q ^ (2 * (↑ℓ + 1))) := by sorry
