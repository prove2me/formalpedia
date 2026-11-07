-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_shift_comm_phase_of_pairing_zero
-- name    : QEC.Coding.FiniteFieldPauli.shift_comm_phase_of_pairing_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:47:17.241298+00:00
-- url     : https://prove2.me/theorems/711c2657-6ece-4e0c-9c4e-57d536a014aa
-- title:
--   Finite Field Pauli: shift comm phase of pairing zero
-- statement:
--   Algebraically orthogonal X/Z words give commuting actual operators.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L368-L373
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L368-L373

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

theorem QEC.Coding.FiniteFieldPauli.shift_comm_phase_of_pairing_zero
    (x z : Word F ι)
    (horth : wordPairing (F := F) (ι := ι) z x = 0) :
    shift x * phase z = phase z * shift x := by sorry
