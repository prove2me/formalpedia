-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_shift_pauli
-- name    : QEC.Coding.FiniteFieldPauli.shift_pauli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:21.998958+00:00
-- url     : https://prove2.me/theorems/d23a94be-0464-48f8-88e2-d1c779c1eb0e
-- title:
--   Finite Field Pauli: shift pauli
-- statement:
--   Translating a Pauli output exposes exactly its character commutator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L807-L817
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L807-L817

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

theorem QEC.Coding.FiniteFieldPauli.shift_pauli (t x z : Word F ι) (ψ : Register F ι) :
    shift t (pauli x z ψ) =
      (character F (wordPairing (F := F) (ι := ι) z t)) •
        pauli x z (shift t ψ) := by sorry
