-- Prove2me | Theorems.Thm_QEC_Coding_QuantumTanner_exists_minimumDistance_of_dimension_pos
-- name    : QEC.Coding.QuantumTanner.exists_minimumDistance_of_dimension_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T00:59:49.924189+00:00
-- url     : https://prove2.me/theorems/ab707a29-8146-4638-b3cf-80355c8a83d7
-- title:
--   Quantum Tanner: exists minimum Distance of dimension pos
-- statement:
--   Positive dimension supplies a nonzero word, so the finite-code minimum
--   is attained rather than an extra input to the global distance argument.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SampleParameters.lean#L23-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuantumTanner/SampleParameters.lean#L23-L30

import Definitions.Def_QEC_Coding_QuantumTanner_Parameters
import Definitions.Def_QEC_Coding_QuantumTanner_SampleParameters
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.QuantumTanner
open Classical QEC.Coding.SmallSetExpansion
universe v

theorem QEC.Coding.QuantumTanner.exists_minimumDistance_of_dimension_pos
    {I : Type v} [Fintype I] (C : LinearCode (ZMod 2) I)
    (hPositive : 0 < Dimension C) : ∃ d : Nat, MinimumDistance C d := by sorry
