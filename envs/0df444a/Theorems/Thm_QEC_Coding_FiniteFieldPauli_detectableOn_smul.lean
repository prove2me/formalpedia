-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_detectableOn_smul
-- name    : QEC.Coding.FiniteFieldPauli.detectableOn_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:05.58395+00:00
-- url     : https://prove2.me/theorems/74251cf3-9af6-4645-afdd-a638be31c4d9
-- title:
--   Finite Field Pauli: detectable On smul
-- statement:
--   Detectability is preserved by a complex scalar multiple.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L754-L764
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L754-L764

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

theorem QEC.Coding.FiniteFieldPauli.detectableOn_smul
    (C : Semantics.QuantumCode (Register F ι))
    (E : Semantics.Operator (Register F ι)) (a : Complex)
    (hE : Semantics.DetectableOn C E) :
    Semantics.DetectableOn C (a • E) := by sorry
