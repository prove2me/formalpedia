-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_exp_neg_four_lt_one_fiftieth
-- name    : QEC.Coding.FiberBundle.RandomPartition.exp_neg_four_lt_one_fiftieth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:25:11.97524+00:00
-- url     : https://prove2.me/theorems/b6d30d68-b16c-4107-b91d-715f7ae0797d
-- title:
--   Random Partition: exp neg four lt one fiftieth
-- statement:
--   Numerical bound used for the paper's `.73` joint-row probability.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2414-L2425
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/PartitionedChecksProbability.lean#L2414-L2425

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

theorem QEC.Coding.FiberBundle.RandomPartition.exp_neg_four_lt_one_fiftieth :
    Real.exp (-4) < (1 : Real) / 50 := by sorry
