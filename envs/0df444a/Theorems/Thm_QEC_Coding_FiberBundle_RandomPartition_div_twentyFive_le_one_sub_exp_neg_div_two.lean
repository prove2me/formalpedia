-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_div_twentyFive_le_one_sub_exp_neg_div_two
-- name    : QEC.Coding.FiberBundle.RandomPartition.div_twentyFive_le_one_sub_exp_neg_div_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:22:21.504196+00:00
-- url     : https://prove2.me/theorems/37eae1cb-b50f-4395-a0db-a2c0af540587
-- title:
--   Random Partition: div twenty Five le one sub exp neg div two
-- statement:
--   On the full HHO20 light-word range `0 ≤ x ≤ 8`, the one-row violation
--   probability has the uniform linear lower bound `x / 25 = .04 x`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L930-L948
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L930-L948

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

theorem QEC.Coding.FiberBundle.RandomPartition.div_twentyFive_le_one_sub_exp_neg_div_two
    (x : Real) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
    x / 25 ≤ (1 - Real.exp (-x)) / 2 := by sorry
