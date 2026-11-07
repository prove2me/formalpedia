-- Prove2me | Theorems.Thm_QEC_Coding_TannerLiftedProduct_sum_jacobiCubePairWeight
-- name    : QEC.Coding.TannerLiftedProduct.sum_jacobiCubePairWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T22:15:47.551389+00:00
-- url     : https://prove2.me/theorems/87dae36f-efdd-4ec6-9bc0-14430862df4d
-- title:
--   Tanner Lifted Product: sum jacobi Cube Pair Weight
-- statement:
--   The parity reindexing turns the signed cube-pair sum into two identical
--   copies of the weighted reindexed sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L160-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiCubeReindex.lean#L160-L180

import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiParityReindex
import Definitions.Def_QEC_Coding_ExpanderCodes_JacobiCubeReindex
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Finset PowerSeries

theorem QEC.Coding.TannerLiftedProduct.sum_jacobiCubePairWeight (n : ℕ) :
    (∑ p : JacobiCubePair n, jacobiCubePairWeight p.1) =
      2 * ∑ p : JacobiReindexedPair n, jacobiReindexedPairWeight p.1 := by sorry
