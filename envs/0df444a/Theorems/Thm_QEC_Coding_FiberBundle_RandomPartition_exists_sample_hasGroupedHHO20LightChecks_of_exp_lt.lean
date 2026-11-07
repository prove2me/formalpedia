-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exists_sample_hasGroupedHHO20LightChecks_of_exp_lt
-- name    : QEC.Coding.FiberBundle.RandomPartition.exists_sample_hasGroupedHHO20LightChecks_of_exp_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:24:10.686645+00:00
-- url     : https://prove2.me/theorems/e1fd21f4-ede6-48eb-a8cc-1ae9ad53aed9
-- title:
--   Random Partition: exists sample has Grouped HHO20 Light Checks of exp lt
-- statement:
--   Light-check existence under the simpler explicit exponential scale
--   condition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2097-L2111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2097-L2111

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

theorem QEC.Coding.FiberBundle.RandomPartition.exists_sample_hasGroupedHHO20LightChecks_of_exp_lt
    (r Delta typeCount : Nat) [NeZero typeCount]
    (hr : 0 < r) (hDeltaHalf : Delta ≤ 2 * r)
    (hTypeDvd : typeCount ∣ 3 * r)
    (hExpSmall :
      Real.exp
          (-(Delta : Real) / (200 * typeCount)) <
        1 / (16 * r * typeCount : Nat)) :
    ∃ sample : Sample r,
      HasGroupedHHO20LightChecks
        (r := r) (typeCount := typeCount) Delta sample := by sorry
