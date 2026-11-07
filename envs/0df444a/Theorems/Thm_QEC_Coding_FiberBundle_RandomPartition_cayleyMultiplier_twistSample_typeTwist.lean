-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_cayleyMultiplier_twistSample_typeTwist
-- name    : QEC.Coding.FiberBundle.RandomPartition.cayleyMultiplier_twistSample_typeTwist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:49.366196+00:00
-- url     : https://prove2.me/theorems/5ce3fd38-4746-47a3-b24c-ebc1ad2bab0e
-- title:
--   Random Partition: cayley Multiplier twist Sample type Twist
-- statement:
--   Replacing the head/tail bits while retaining every sampled type twist
--   leaves the Cayley multiplier unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4232-L4242
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4232-L4242

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

theorem QEC.Coding.FiberBundle.RandomPartition.cayleyMultiplier_twistSample_typeTwist
    {r typeCount ell : Nat} [NeZero ell]
    (partitionSample : Sample r)
    (spectrumSample : RandomTwist.Sample r typeCount ell)
    (frequency : ZMod ell) :
    TwistGraph.cayleyMultiplier
        (twistSample partitionSample
          (fun τ => RandomTwist.typeTwist spectrumSample τ))
        frequency =
      TwistGraph.cayleyMultiplier spectrumSample frequency := by sorry
