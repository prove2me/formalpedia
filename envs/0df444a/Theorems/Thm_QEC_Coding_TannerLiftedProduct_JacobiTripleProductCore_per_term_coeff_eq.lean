-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_per_term_coeff_eq
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.per_term_coeff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:16:51.445195+00:00
-- url     : https://prove2.me/theorems/f2032149-4f4b-4274-8bb3-43656fdb741b
-- title:
--   Jacobi Triple Product Core: per term coeff eq
-- statement:
--   The Jacobi Triple Product Core construction uses the per term coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1781-L1804
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1781-L1804

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.per_term_coeff_eq (j d ℓ : ℕ) :
    (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) =
    ((-A_hahn j) ^ ℓ * Q₀ ^ (ℓ.choose 2) * V ℓ).coeff
      ((d : ℤ) - ((j + 1 : ℤ)) ^ 2) := by sorry
