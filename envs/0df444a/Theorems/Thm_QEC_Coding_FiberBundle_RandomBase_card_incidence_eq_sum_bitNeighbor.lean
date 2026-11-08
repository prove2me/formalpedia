-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_incidence_eq_sum_bitNeighbor
-- name    : QEC.Coding.FiberBundle.RandomBase.card_incidence_eq_sum_bitNeighbor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:27:19.053799+00:00
-- url     : https://prove2.me/theorems/520914e8-6545-46c3-958f-46f34202449f
-- title:
--   Random Base: card incidence eq sum bit Neighbor
-- statement:
--   Direct incidence count for an arbitrary Tanner relation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L282-L305
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L282-L305

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
import Theorems.Thm_QEC_Coding_FiberBundle_card_incidence_eq_sum_bitNeighbor

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.card_incidence_eq_sum_bitNeighbor
    {Check Bit : Type*} [Fintype Check] [DecidableEq Check]
    [Fintype Bit] [DecidableEq Bit]
    (R : Check → Bit → Prop) [DecidableRel R] :
    Fintype.card (ClassicalWeightReduction.Incidence R) =
      ∑ b : Bit,
        Fintype.card (ClassicalWeightReduction.BitNeighbor R b) := by sorry
