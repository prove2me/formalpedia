-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_hho20_typeCount_small
-- name    : QEC.Coding.FiberBundle.RandomPartition.hho20_typeCount_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:55:56.928628+00:00
-- url     : https://prove2.me/theorems/3b97d295-4e37-47e1-8304-81b762c867c5
-- title:
--   Random Partition: hho20 type Count small
-- statement:
--   Type enumeration is negligible compared with the base scale.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L948-L960
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L948-L960

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.hho20_typeCount_small
    (s : Nat) (hs : 200 ≤ s) :
    (100 : Real) * hho20TypeCount s ≤
      hho20BaseScale s := by sorry
