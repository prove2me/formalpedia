-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_tsum_coeff_congr_of_per_term
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_coeff_congr_of_per_term
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:13:28.335124+00:00
-- url     : https://prove2.me/theorems/bd89785d-5dff-4bb6-9ef6-419da3e2677d
-- title:
--   Jacobi Triple Product Core: tsum coeff congr of per term
-- statement:
--   The Jacobi Triple Product Core construction uses the tsum coeff congr of per term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1028-L1036
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1028-L1036

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.tsum_coeff_congr_of_per_term (x : R) (m : ℕ) : letI := piTop;
    (∑' k : ℕ, qPochhammerInf (q ^ 2) (q ^ 2) *
      (q ^ (k ^ 2) * x ^ k *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) k) 1) : R).coeff m =
    (∑' k : ℕ, q ^ (k ^ 2) * x ^ k *
      qPochhammerInf (q ^ 2 * (q ^ 2) ^ k) (q ^ 2) : R).coeff m := by sorry
