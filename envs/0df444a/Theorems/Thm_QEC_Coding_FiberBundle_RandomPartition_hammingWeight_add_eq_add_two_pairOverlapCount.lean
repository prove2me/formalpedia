-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hammingWeight_add_eq_add_two_pairOverlapCount
-- name    : QEC.Coding.FiberBundle.RandomPartition.hammingWeight_add_eq_add_two_pairOverlapCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:19:18.68322+00:00
-- url     : https://prove2.me/theorems/016c8b98-448f-48c1-ac31-480ec0afa3a7
-- title:
--   Random Partition: hamming Weight add eq add two pair Overlap Count
-- statement:
--   Binary support arithmetic: the two input supports decompose into their
--   XOR support plus two copies of their overlap.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L825-L868
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L825-L868

import Definitions.Def_QEC_Coding_FiberBundle_TwistGraphSpectrumProbability
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Rank
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_Distance
import Definitions.Def_QEC_Coding_FiberBundle_RandomBase_ExpansionProbability
import Mathlib.Probability.Independence.Integration
import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition
open scoped BigOperators
open MeasureTheory

theorem QEC.Coding.FiberBundle.RandomPartition.hammingWeight_add_eq_add_two_pairOverlapCount
    {r : Nat}
    (y z : Word (ZMod 2) (Fin (4 * r))) :
    HammingWeight y + HammingWeight z =
      HammingWeight (y + z) + 2 * pairOverlapCount y z := by sorry
