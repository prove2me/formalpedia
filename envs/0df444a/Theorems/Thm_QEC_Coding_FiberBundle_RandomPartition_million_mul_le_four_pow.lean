-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_million_mul_le_four_pow
-- name    : QEC.Coding.FiberBundle.RandomPartition.million_mul_le_four_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:57:17.033185+00:00
-- url     : https://prove2.me/theorems/7227ae21-2fff-4751-8552-6de9f3d0f27f
-- title:
--   Random Partition: million mul le four pow
-- statement:
--   Elementary exponential domination used to keep the expected degree below
--   half the base size.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L809-L819
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L809-L819

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.million_mul_le_four_pow
    (s : Nat) (hs : 20 ≤ s) :
    1000000 * s ≤ 4 ^ s := by sorry
