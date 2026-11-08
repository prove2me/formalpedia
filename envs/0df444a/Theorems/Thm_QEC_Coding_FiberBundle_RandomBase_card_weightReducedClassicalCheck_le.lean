-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_weightReducedClassicalCheck_le
-- name    : QEC.Coding.FiberBundle.RandomBase.card_weightReducedClassicalCheck_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:58.185111+00:00
-- url     : https://prove2.me/theorems/9697fe26-aa07-4356-abbb-feab763ba71b
-- title:
--   Random Base: card weight Reduced Classical Check le
-- statement:
--   The number of reduced classical checks obeys the analogous explicit
--   degree-window bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L398-L427
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L398-L427

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.card_weightReducedClassicalCheck_le
    {r Delta : Nat} (sample : Sample r)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Fintype.card
        (ClassicalWeightReduction.WeightReducedCheck
          (incidenceRelation sample)) ≤
      808 * r * Delta := by sorry
