-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_minimumDistance_ge_of_ceil_lower_bound
-- name    : QEC.Coding.QuantumTanner.minimumDistance_ge_of_ceil_lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:59:57.585319+00:00
-- url     : https://prove2.me/theorems/b4e0aac7-578b-4067-acaf-8d79ab753e24
-- title:
--   Quantum Tanner: minimum Distance ge of ceil lower bound
-- statement:
--   An attained local minimum inherits the real GV budget of the event.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SampleParameters.lean#L33-L38
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SampleParameters.lean#L33-L38

import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe v

theorem QEC.Coding.QuantumTanner.minimumDistance_ge_of_ceil_lower_bound
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I)
    (bound : ℝ) (d : Nat) (hLower : HasMinimumDistanceAtLeast C (Nat.ceil bound))
    (hMinimum : MinimumDistance C d) : bound ≤ (d : ℝ) := by sorry
