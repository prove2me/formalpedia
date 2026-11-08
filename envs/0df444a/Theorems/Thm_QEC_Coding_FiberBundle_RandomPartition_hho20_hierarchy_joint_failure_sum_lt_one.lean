-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_hierarchy_joint_failure_sum_lt_one
-- name    : QEC.Coding.FiberBundle.RandomPartition.hho20_hierarchy_joint_failure_sum_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:54:58.340217+00:00
-- url     : https://prove2.me/theorems/400a86b5-d6d1-40fb-acf2-7c703440135c
-- title:
--   Random Partition: hho20 hierarchy joint failure sum lt one
-- statement:
--   All four random-base estimates and both partition estimates fit inside
--   the unit probability budget for the explicit hierarchy.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L964-L989
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L964-L989

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.hho20_hierarchy_joint_failure_sum_lt_one
    (s : Nat) (hs : 200 ≤ s) :
    letI : NeZero (hho20TypeCount s) :=
      ⟨hho20TypeCount_ne_zero s (by omega)⟩
    (fullyGoodBaseFailureBound
        (hho20BaseScale s) (hho20DegreeScale s)).toReal +
        ((hho20TypeCount s : Real) *
            ((1 +
              Real.exp
                (-(hho20DegreeScale s : Real) /
                  (200 * hho20TypeCount s))) ^
                    (8 * hho20BaseScale s) - 1) +
          Real.exp (-(hho20BaseScale s : Real) / 10)) <
      1 := by sorry
