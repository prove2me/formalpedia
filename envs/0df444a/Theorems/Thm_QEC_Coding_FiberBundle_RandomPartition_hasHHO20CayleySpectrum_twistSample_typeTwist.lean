-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hasHHO20CayleySpectrum_twistSample_typeTwist
-- name    : QEC.Coding.FiberBundle.RandomPartition.hasHHO20CayleySpectrum_twistSample_typeTwist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:09.980256+00:00
-- url     : https://prove2.me/theorems/c2bb9144-e713-457f-a4ce-3d0e67fd615a
-- title:
--   Random Partition: has HHO20 Cayley Spectrum twist Sample type Twist
-- statement:
--   The spectrum event depends only on type twists, so it survives assembly
--   with independently selected partition bits.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4246-L4256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L4246-L4256

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

theorem QEC.Coding.FiberBundle.RandomPartition.hasHHO20CayleySpectrum_twistSample_typeTwist
    {r typeCount ell : Nat} [NeZero ell]
    (partitionSample : Sample r)
    (spectrumSample : RandomTwist.Sample r typeCount ell)
    (hSpectrum : TwistGraph.HasHHO20CayleySpectrum spectrumSample) :
    TwistGraph.HasHHO20CayleySpectrum
      (twistSample partitionSample
        (fun τ => RandomTwist.typeTwist spectrumSample τ)) := by sorry
