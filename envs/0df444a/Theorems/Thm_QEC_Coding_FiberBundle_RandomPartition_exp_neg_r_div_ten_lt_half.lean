-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_r_div_ten_lt_half
-- name    : QEC.Coding.FiberBundle.RandomPartition.exp_neg_r_div_ten_lt_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:26:55.500139+00:00
-- url     : https://prove2.me/theorems/96a1938b-b595-4587-a667-8dd53a69908e
-- title:
--   Random Partition: exp neg r div ten lt half
-- statement:
--   Once `r ≥ 7`, the remaining heavy failure exponential is below one
--   half.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3796-L3811
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L3796-L3811

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

theorem QEC.Coding.FiberBundle.RandomPartition.exp_neg_r_div_ten_lt_half
    (r : Nat) (hr : 7 ≤ r) :
    Real.exp (-(r : Real) / 10) < (1 : Real) / 2 := by sorry
