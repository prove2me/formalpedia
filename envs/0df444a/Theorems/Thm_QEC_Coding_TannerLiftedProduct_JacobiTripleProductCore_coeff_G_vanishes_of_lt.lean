-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_coeff_G_vanishes_of_lt
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_G_vanishes_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:15:00.584054+00:00
-- url     : https://prove2.me/theorems/b7020424-4ab2-4488-a59c-d72b51c391fb
-- title:
--   Jacobi Triple Product Core: coeff G vanishes of lt
-- statement:
--   The Jacobi Triple Product Core construction uses the coeff G vanishes of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1479-L1483
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1479-L1483

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.coeff_G_vanishes_of_lt (j ℓ d : ℕ) (h : d < N_exp j ℓ) :
    (PowerSeries.coeff d)
      ((-1 : R) ^ ℓ * q ^ ((-(↑j + 1 : ℤ) + ↑ℓ).natAbs ^ 2 + ℓ) *
       PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) ℓ) 1) = 0 := by sorry
