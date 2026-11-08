-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_card_weightReducedClassicalSides_le_two_mul_incidence
-- name    : QEC.Coding.FiberBundle.RandomBase.card_weightReducedClassicalSides_le_two_mul_incidence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:24:01.02205+00:00
-- url     : https://prove2.me/theorems/274ccac1-0306-426b-a98a-f51650843068
-- title:
--   Random Base: card weight Reduced Classical Sides le two mul incidence
-- statement:
--   Both sides of classical weight reduction contain at most two copies of
--   the original incidence set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L309-L361
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L309-L361

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.card_weightReducedClassicalSides_le_two_mul_incidence
    {Check Bit : Type*} [Fintype Check] [DecidableEq Check]
    [Fintype Bit] [DecidableEq Bit]
    (R : Check → Bit → Prop) [DecidableRel R] :
    Fintype.card (ClassicalWeightReduction.WeightReducedBit R) ≤
        2 * Fintype.card (ClassicalWeightReduction.Incidence R) ∧
      Fintype.card (ClassicalWeightReduction.WeightReducedCheck R) ≤
        2 * Fintype.card (ClassicalWeightReduction.Incidence R) := by sorry
