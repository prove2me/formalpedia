-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_phase_finset_sum_fixed
-- name    : QEC.Coding.FiniteFieldPauli.phase_finset_sum_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:47:08.566639+00:00
-- url     : https://prove2.me/theorems/df0adf13-318b-47f1-a4a5-afbc34c82f85
-- title:
--   Finite Field Pauli: phase finset sum fixed
-- statement:
--   A vector fixed by every phase in a finite family is fixed by their sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L278-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L278-L293

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

theorem QEC.Coding.FiniteFieldPauli.phase_finset_sum_fixed
    {κ : Type*} (s : Finset κ) (f : κ → Word F ι) (ψ : Register F ι)
    (hfixed : ∀ k ∈ s, phase (f k) ψ = ψ) :
    phase (∑ k ∈ s, f k) ψ = ψ := by sorry
