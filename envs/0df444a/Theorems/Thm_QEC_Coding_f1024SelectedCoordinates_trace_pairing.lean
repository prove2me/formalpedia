-- Prove2me | Theorems.Thm_QEC_Coding_f1024SelectedCoordinates_trace_pairing
-- name    : QEC.Coding.f1024SelectedCoordinates_trace_pairing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T11:16:57.056458+00:00
-- url     : https://prove2.me/theorems/f42592cc-c744-4282-acb7-5b4ab4708ca4
-- title:
--   Coding: f1024 Selected Coordinates trace pairing
-- statement:
--   The source's self-dual basis turns the field trace pairing into binary word pairing.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L181-L224
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/QuditQubitConversion/Transport.lean#L181-L224

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Coding_QuditQubitConversion_SelfDualBasis
import Definitions.Def_QEC_Coding_QuditQubitConversion_Transport
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding
open scoped BigOperators

theorem QEC.Coding.f1024SelectedCoordinates_trace_pairing (γ η : F1024) :
    Algebra.trace (ZMod 2) F1024 (γ * η) =
      wordPairing (F := ZMod 2) (ι := Fin 10)
        (f1024SelectedCoordinates γ) (f1024SelectedCoordinates η) := by sorry
