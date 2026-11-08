-- Prove2me | Theorems.Thm_QEC_Coding_FiberBundle_RandomPartition_five_dvd_hho20BaseScale
-- name    : QEC.Coding.FiberBundle.RandomPartition.five_dvd_hho20BaseScale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T08:54:41.445404+00:00
-- url     : https://prove2.me/theorems/b6a2406f-c740-4f5b-91d8-3aefa04eff3f
-- title:
--   Random Partition: five dvd hho20 Base Scale
-- statement:
--   The base scale is a multiple of five, as used to group the distance
--   tail.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L852-L857
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiberBundle/ExplicitFamily/Parameters.lean#L852-L857

import Definitions.Def_QEC_Coding_FiberBundle_PartitionedChecksProbability
import Definitions.Def_QEC_Coding_FiberBundle_ExplicitFamily_Parameters
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle QEC.Coding.FiberBundle.RandomPartition

theorem QEC.Coding.FiberBundle.RandomPartition.five_dvd_hho20BaseScale (s : Nat) :
    5 ∣ hho20BaseScale s := by sorry
