-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomBase_weightReducedClassical_rowWeight_le_three
-- name    : QEC.Coding.FiberBundle.RandomBase.weightReducedClassical_rowWeight_le_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T09:30:42.399486+00:00
-- url     : https://prove2.me/theorems/84c0fec3-4368-42dd-bb54-ef0007ae2ee5
-- title:
--   Random Base: weight Reduced Classical row Weight le three
-- statement:
--   Every row of the extracted balancing matrix has weight at most three.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L258-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ClassicalLDPCBalance.lean#L258-L268

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_FiberBundle_ClassicalLDPCBalance
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomBase
open QEC.Coding
universe u v w

theorem QEC.Coding.FiberBundle.RandomBase.weightReducedClassical_rowWeight_le_three
    {r : Nat} (sample : Sample r)
    (q : ClassicalWeightReduction.WeightReducedCheck
      (incidenceRelation sample)) :
    HammingWeight
      (wordLinearMapTranspose
        (ClassicalWeightReduction.boundary (F := ZMod 2)
          (incidenceRelation sample))
        (Pi.single q 1)) ≤ 3 := by sorry
