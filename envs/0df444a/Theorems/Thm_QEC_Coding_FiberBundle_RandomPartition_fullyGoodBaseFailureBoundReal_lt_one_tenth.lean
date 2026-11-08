-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_fullyGoodBaseFailureBoundReal_lt_one_tenth
-- name    : QEC.Coding.FiberBundle.RandomPartition.fullyGoodBaseFailureBoundReal_lt_one_tenth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:53:48.064341+00:00
-- url     : https://prove2.me/theorems/38cdb23e-5b51-41c6-82d6-4acc0496c450
-- title:
--   Random Partition: fully Good Base Failure Bound Real lt one tenth
-- statement:
--   Six explicit one-percent estimates are enough to place the complete
--   random-base failure envelope below one tenth.  These hypotheses are analytic
--   subgoals only; the parameter family below discharges them.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L138-L203
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L138-L203

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.fullyGoodBaseFailureBoundReal_lt_one_tenth
    (r Delta : Nat)
    (hr : 500 ≤ r) (hFive : 5 ∣ r)
    (hDegree :
      (14 * r : Real) * Real.exp (-(Delta : Real) / 40000) <
        1 / 100)
    (hRank :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 2) <
        1 / 200)
    (hDistance :
      (4 * r : Real) *
          Real.exp (-(3 : Real) * Delta / 28) <
        1 / 200)
    (hExpansion :
      (3 * r : Real) * Real.exp (-(Delta : Real) / 1000) <
        1 / 200) :
    fullyGoodBaseFailureBoundReal r Delta < 1 / 10 := by sorry
