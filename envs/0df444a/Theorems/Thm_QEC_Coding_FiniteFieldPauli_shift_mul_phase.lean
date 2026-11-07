-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_shift_mul_phase
-- name    : QEC.Coding.FiniteFieldPauli.shift_mul_phase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:46:26.526132+00:00
-- url     : https://prove2.me/theorems/2d59d6e3-0490-48f3-8485-86ad3dd2ae87
-- title:
--   Finite Field Pauli: shift mul phase
-- statement:
--   The field-valued word pairing is the exact X/Z commutation exponent.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L355-L365
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L355-L365

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

theorem QEC.Coding.FiniteFieldPauli.shift_mul_phase (x z : Word F ι) :
    shift x * phase z =
      (character F (wordPairing (F := F) (ι := ι) z x)) •
        (phase z * shift x) := by sorry
