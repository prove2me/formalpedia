-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_shift_finset_sum_fixed
-- name    : QEC.Coding.FiniteFieldPauli.shift_finset_sum_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:46:03.533188+00:00
-- url     : https://prove2.me/theorems/0bc872a0-481e-4c13-b856-7dc5cbc9b6b9
-- title:
--   Finite Field Pauli: shift finset sum fixed
-- statement:
--   A vector fixed by every shift in a finite family is fixed by their sum.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L260-L275
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L260-L275

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

theorem QEC.Coding.FiniteFieldPauli.shift_finset_sum_fixed
    {κ : Type*} (s : Finset κ) (f : κ → Word F ι) (ψ : Register F ι)
    (hfixed : ∀ k ∈ s, shift (f k) ψ = ψ) :
    shift (∑ k ∈ s, f k) ψ = ψ := by sorry
