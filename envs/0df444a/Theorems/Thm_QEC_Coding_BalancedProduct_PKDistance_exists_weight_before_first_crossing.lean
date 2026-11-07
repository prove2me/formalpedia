-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_PKDistance_exists_weight_before_first_crossing
-- name    : QEC.Coding.BalancedProduct.PKDistance.exists_weight_before_first_crossing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T06:59:15.407634+00:00
-- url     : https://prove2.me/theorems/7a9396cf-0f44-4cd4-abce-e6beda60d5e5
-- title:
--   PKDistance: exists weight before first crossing
-- statement:
--   A finite sequence that starts below a threshold and ends above it has a
--   first crossing.  If every step has weight at most `stepBound`, the word just
--   before that crossing is within `stepBound` of the threshold.
--
--   This is the minimal-`t₀` combinatorial step in [PK20, Proposition 2, Case 1].
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L366-L390
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/PKDistance.lean#L366-L390

import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
import Definitions.Def_QEC_Coding_BalancedProduct_LiftedProductDuality
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Definitions.Def_QEC_Coding_FiberBundle_CohomologyRepresentatives
import Definitions.Def_QEC_Coding_FiberBundle_HomologyRepresentatives
import Definitions.Def_QEC_Coding_BalancedProduct_PKDistance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.PKDistance
open QEC.Coding
universe u v w

theorem QEC.Coding.BalancedProduct.PKDistance.exists_weight_before_first_crossing
    {ι : Type u} [Fintype ι]
    (sequence : Nat → Word (ZMod 2) ι)
    (last threshold stepBound : Nat)
    (hstart : HammingWeight (sequence 0) < threshold)
    (hend : threshold ≤ HammingWeight (sequence last))
    (hstep : ∀ t < last,
      HammingWeight (sequence (t + 1) + sequence t) ≤ stepBound) :
    ∃ t < last,
      HammingWeight (sequence t) < threshold ∧
      threshold ≤ HammingWeight (sequence (t + 1)) ∧
      threshold ≤ HammingWeight (sequence t) + stepBound := by sorry
