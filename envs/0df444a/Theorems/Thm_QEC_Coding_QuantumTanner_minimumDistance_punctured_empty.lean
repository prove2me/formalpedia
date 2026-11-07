-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_minimumDistance_punctured_empty
-- name    : QEC.Coding.QuantumTanner.minimumDistance_punctured_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:13:09.895909+00:00
-- url     : https://prove2.me/theorems/069ae2c3-5846-4139-8695-dc73e509f0f6
-- title:
--   Quantum Tanner: minimum Distance punctured empty
-- statement:
--   An attained minimum is unchanged by deleting the empty coordinate set.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/RobustnessTransport.lean#L38-L57
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/RobustnessTransport.lean#L38-L57

import Definitions.Def_QEC_Coding_QuantumTanner_Core
import Definitions.Def_QEC_Coding_QuantumTanner_RobustnessTransport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical
universe u v

theorem QEC.Coding.QuantumTanner.minimumDistance_punctured_empty
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I)
    {d : Nat} (h : MinimumDistance C d) :
    MinimumDistance (puncturedCode C ∅) d := by sorry
