-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summand_rhs_E_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_rhs_E_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:39.011363+00:00
-- url     : https://prove2.me/theorems/66184080-e229-4783-abd7-dd01b8deb866
-- title:
--   Jacobi Triple Product Core: summand rhs E eq
-- statement:
--   The Jacobi Triple Product Core construction uses the summand rhs E eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1356-L1374
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1356-L1374

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_rhs_E_eq (m : ℤ) (ℓ : ℕ) :
    (PowerSeries.C (LaurentPolynomial.T m) * q ^ m.natAbs ^ 2) *
    ((-(q * aI)) ^ ℓ * PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    PowerSeries.C (LaurentPolynomial.T (m - ↑ℓ)) *
    ((-1 : R) ^ ℓ * q ^ (m.natAbs ^ 2 + ℓ)) *
    PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by sorry
