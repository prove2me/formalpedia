-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_rank_decay_lt
-- name    : QEC.Coding.FiberBundle.RandomPartition.hho20_rank_decay_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:54:09.681816+00:00
-- url     : https://prove2.me/theorems/efc8ab1d-d72a-4359-9a24-6f5e5b433afa
-- title:
--   Random Partition: hho20 rank decay lt
-- statement:
--   The small-support rank contribution of the explicit hierarchy is below
--   one half percent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L664-L699
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L664-L699

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.hho20_rank_decay_lt
    (s : Nat) (hs : 200 ≤ s) :
    (3 * hho20BaseScale s : Real) *
        Real.exp (-(hho20DegreeScale s : Real) / 2) <
      1 / 200 := by sorry
