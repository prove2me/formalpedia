-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_detectableOn_add
-- name    : QEC.Coding.FiniteFieldPauli.detectableOn_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:47:53.792438+00:00
-- url     : https://prove2.me/theorems/cd8e3afe-8603-4ae9-8f69-e0d6827587e5
-- title:
--   Finite Field Pauli: detectable On add
-- statement:
--   Detectability is preserved by adding two operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L767-L779
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L767-L779

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteAlphabetLocality
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Coding_QLDPC_BPTMeasurementDistance
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditMatrixElements
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.FieldTheory.Finiteness
import Mathlib.NumberTheory.LegendreSymbol.Complex
import Definitions.Def_QEC_Coding_Stabilizer_FiniteFieldPauli
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.FiniteFieldPauli
open Classical
universe u v
variable {F : Type u} {ι : Type v} [Field F] [Fintype F] [Fintype ι]

theorem QEC.Coding.FiniteFieldPauli.detectableOn_add
    (C : Semantics.QuantumCode (Register F ι))
    (E G : Semantics.Operator (Register F ι))
    (hE : Semantics.DetectableOn C E)
    (hG : Semantics.DetectableOn C G) :
    Semantics.DetectableOn C (E + G) := by sorry
