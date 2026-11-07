-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_sum_quotientCosetKet_of_shift_fixed
-- name    : QEC.Coding.FiniteFieldPauli.sum_quotientCosetKet_of_shift_fixed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:55:02.051573+00:00
-- url     : https://prove2.me/theorems/d55921db-05f8-43b8-a56f-b2bf14d041c2
-- title:
--   Finite Field Pauli: sum quotient Coset Ket of shift fixed
-- statement:
--   X-shift-invariant wavefunctions are reconstructed from their coset amplitudes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1306-L1325
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1306-L1325

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

theorem QEC.Coding.FiniteFieldPauli.sum_quotientCosetKet_of_shift_fixed (xCode : LinearCode F ι)
    (ψ : Register F ι)
    (hfixed : ∀ η x : Word F ι, x ∈ xCode.carrier → ψ (η + x) = ψ η) :
    (∑ q : Word F ι ⧸ xCode.carrier,
      ψ (Quotient.out q) • quotientCosetKet xCode q) = ψ := by sorry
