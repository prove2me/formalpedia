-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_eq_smul_of_detectable_of_preserves
-- name    : QEC.Coding.FiniteFieldPauli.eq_smul_of_detectable_of_preserves
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:45:07.501191+00:00
-- url     : https://prove2.me/theorems/2bb9fc92-ed59-4614-b2c7-432e6df86237
-- title:
--   Finite Field Pauli: eq smul of detectable of preserves
-- statement:
--   A detectable code-preserving operator has one scalar action on every code state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L976-L988
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L976-L988

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

theorem QEC.Coding.FiniteFieldPauli.eq_smul_of_detectable_of_preserves
    (C : Semantics.QuantumCode (Register F ι))
    (E : Semantics.Operator (Register F ι))
    (hdetect : Semantics.DetectableOn C E)
    (hpreserve : ∀ ψ : Register F ι, ψ ∈ C.carrier → E ψ ∈ C.carrier) :
    ∃ c : Complex, ∀ ψ : Register F ι, ψ ∈ C.carrier → E ψ = c • ψ := by sorry
