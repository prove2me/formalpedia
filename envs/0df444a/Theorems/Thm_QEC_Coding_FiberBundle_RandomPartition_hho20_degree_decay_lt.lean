-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_degree_decay_lt
-- name    : QEC.Coding.FiberBundle.RandomPartition.hho20_degree_decay_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:54:31.889583+00:00
-- url     : https://prove2.me/theorems/72e6d631-22db-4ca3-8de6-45688887af0b
-- title:
--   Random Partition: hho20 degree decay lt
-- statement:
--   The degree-window contribution of the explicit hierarchy is below one
--   percent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L626-L660
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L626-L660

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.hho20_degree_decay_lt
    (s : Nat) (hs : 200 ≤ s) :
    (14 * hho20BaseScale s : Real) *
        Real.exp (-(hho20DegreeScale s : Real) / 40000) <
      1 / 100 := by sorry
