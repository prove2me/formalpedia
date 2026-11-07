-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_IsRobustWithPunctureResistance_isRobust
-- name    : QEC.Coding.QuantumTanner.IsRobustWithPunctureResistance.isRobust
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:24:34.84836+00:00
-- url     : https://prove2.me/theorems/0525af86-f29c-44c4-98a8-cf26f400b4ff
-- title:
--   Is Robust With Puncture Resistance: is Robust
-- statement:
--   Puncture resistance includes ordinary robustness, with the original
--   minimum distances and the exact original support-cover bounds.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/RobustnessTransport.lean#L78-L107
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/RobustnessTransport.lean#L78-L107

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v

theorem QEC.Coding.QuantumTanner.IsRobustWithPunctureResistance.isRobust
    {A B : Type v} [Fintype A] [Fintype B]
    {CA : LinearCode (ZMod 2) A} {CB : LinearCode (ZMod 2) B}
    {w p : Nat} (h : IsRobustWithPunctureResistance CA CB w p) :
    IsRobust CA CB w := by sorry
