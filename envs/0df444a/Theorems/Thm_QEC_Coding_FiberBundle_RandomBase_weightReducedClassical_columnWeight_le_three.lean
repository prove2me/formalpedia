-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_weightReducedClassical_columnWeight_le_three
-- name    : QEC.Coding.FiberBundle.RandomBase.weightReducedClassical_columnWeight_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:50.420556+00:00
-- url     : https://prove2.me/theorems/de882bb1-0706-48c8-b4bb-9c765e7fe72c
-- title:
--   Random Base: weight Reduced Classical column Weight le three
-- statement:
--   Every column of the extracted balancing matrix has weight at most three.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L271-L279
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L271-L279

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.weightReducedClassical_columnWeight_le_three
    {r : Nat} (sample : Sample r)
    (b : ClassicalWeightReduction.WeightReducedBit
      (incidenceRelation sample)) :
    HammingWeight
      (ClassicalWeightReduction.boundary (F := ZMod 2)
        (incidenceRelation sample) (Pi.single b 1)) ≤ 3 := by sorry
