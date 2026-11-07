-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_JacobiTripleProductCore_summable_product_terms
-- name    : QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_product_terms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T09:14:33.545198+00:00
-- url     : https://prove2.me/theorems/9d732791-9840-467c-87c6-fa5cdc8f16b7
-- title:
--   Jacobi Triple Product Core: summable product terms
-- statement:
--   The Jacobi Triple Product Core construction uses the summable product terms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1340-L1354
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiTripleProductCore.lean#L1340-L1354

import Mathlib
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiTripleProductCore
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore
attribute [local instance] QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore._p2m_local_instance_23589ab013_50
open PowerSeries
set_option maxHeartbeats 800000

theorem QEC.Coding.TannerLiftedProduct.JacobiTripleProductCore.summable_product_terms : letI := piTop;
    Summable (fun p : ℤ × ℕ =>
      (PowerSeries.C (LaurentPolynomial.T p.1) * q ^ p.1.natAbs ^ 2) *
      ((-(q * aI)) ^ p.2 *
        PowerSeries.invOfUnit (qPoch (q ^ 2) (q ^ 2) p.2) 1)) := by sorry
