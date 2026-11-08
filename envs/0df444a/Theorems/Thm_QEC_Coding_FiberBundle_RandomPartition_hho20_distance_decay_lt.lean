-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_distance_decay_lt
-- name    : QEC.Coding.FiberBundle.RandomPartition.hho20_distance_decay_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:54:56.794745+00:00
-- url     : https://prove2.me/theorems/a14f7a3c-63ac-41c6-8197-9148a7fabee0
-- title:
--   Random Partition: hho20 distance decay lt
-- statement:
--   The small-support distance contribution of the explicit hierarchy is
--   below one half percent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L703-L739
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L703-L739

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.hho20_distance_decay_lt
    (s : Nat) (hs : 200 ≤ s) :
    (4 * hho20BaseScale s : Real) *
        Real.exp
          (-(3 : Real) * hho20DegreeScale s / 28) <
      1 / 200 := by sorry
