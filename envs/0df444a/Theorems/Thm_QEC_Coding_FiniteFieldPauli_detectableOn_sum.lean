-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_detectableOn_sum
-- name    : QEC.Coding.FiniteFieldPauli.detectableOn_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:47:58.667437+00:00
-- url     : https://prove2.me/theorems/3fe607eb-62ed-4a00-a89b-79ef4d561c48
-- title:
--   Finite Field Pauli: detectable On sum
-- statement:
--   Detectability is preserved by a finite operator sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L782-L797
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L782-L797

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

theorem QEC.Coding.FiniteFieldPauli.detectableOn_sum {α : Type*}
    (C : Semantics.QuantumCode (Register F ι))
    (s : Finset α) (E : α → Semantics.Operator (Register F ι))
    (hE : ∀ a ∈ s, Semantics.DetectableOn C (E a)) :
    Semantics.DetectableOn C (∑ a ∈ s, E a) := by sorry
