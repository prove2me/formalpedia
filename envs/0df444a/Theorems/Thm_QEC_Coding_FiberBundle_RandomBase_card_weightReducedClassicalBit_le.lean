-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_weightReducedClassicalBit_le
-- name    : QEC.Coding.FiberBundle.RandomBase.card_weightReducedClassicalBit_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:31:15.428799+00:00
-- url     : https://prove2.me/theorems/7ee0b2ce-6b2a-475f-a34b-cf76b89c3b8b
-- title:
--   Random Base: card weight Reduced Classical Bit le
-- statement:
--   The number of reduced classical bits is controlled explicitly by the
--   sample degree window.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L365-L394
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L365-L394

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.card_weightReducedClassicalBit_le
    {r Delta : Nat} (sample : Sample r)
    (hGood : IsFullyGood (Delta := Delta) sample) :
    Fintype.card
        (ClassicalWeightReduction.WeightReducedBit
          (incidenceRelation sample)) ≤
      808 * r * Delta := by sorry
