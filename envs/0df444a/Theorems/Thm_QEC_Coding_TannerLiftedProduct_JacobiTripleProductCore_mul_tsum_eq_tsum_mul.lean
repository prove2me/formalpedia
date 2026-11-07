-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_mul_tsum_eq_tsum_mul
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.mul_tsum_eq_tsum_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:07.948839+00:00
-- url     : https://prove2.me/theorems/982ec7e5-ec88-43eb-adcf-dd0355fa67e7
-- title:
--   Jacobi Triple Product Core: mul tsum eq tsum mul
-- statement:
--   The Jacobi Triple Product Core construction uses the mul tsum eq tsum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L979-L989
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L979-L989

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.mul_tsum_eq_tsum_mul (x : R) : letI := piTop;
    (qPochhammerInf (q ^ 2) (q ^ 2) *
      (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R) =
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R) := by sorry
