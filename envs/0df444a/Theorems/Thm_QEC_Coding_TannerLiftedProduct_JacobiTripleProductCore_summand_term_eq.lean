-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summand_term_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_term_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:59.738692+00:00
-- url     : https://prove2.me/theorems/d873971b-ef14-41e0-9058-7a38f0bced3d
-- title:
--   Jacobi Triple Product Core: summand term eq
-- statement:
--   The Jacobi Triple Product Core construction uses the summand term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1078-L1094
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1078-L1094

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summand_term_eq (k ℓ : ℕ) :
    q ^ (k ^ 2) * PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ (ℓ ^ 2 + ℓ + 2 * k * ℓ) *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    PowerSeries.C (LaurentPolynomial.T (k : ℤ)) *
      ((-1 : R) ^ ℓ * q ^ ((k + ℓ) ^ 2 + ℓ)) *
      PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1 := by sorry
