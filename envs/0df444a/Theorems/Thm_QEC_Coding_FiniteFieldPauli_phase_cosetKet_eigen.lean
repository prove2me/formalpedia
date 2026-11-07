-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_phase_cosetKet_eigen
-- name    : QEC.Coding.FiniteFieldPauli.phase_cosetKet_eigen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:45:25.045635+00:00
-- url     : https://prove2.me/theorems/e2a8f317-d05a-4d03-8304-04d175357a9a
-- title:
--   Finite Field Pauli: phase coset Ket eigen
-- statement:
--   A Z-Pauli commuting with X checks is diagonal on the X-coset states.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L494-L508
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L494-L508

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

theorem QEC.Coding.FiniteFieldPauli.phase_cosetKet_eigen (xCode : LinearCode F ι)
    (z a : Word F ι) (hz : z ∈ xCode.dual.carrier) :
    phase z (cosetKet xCode a) =
      (character F (wordPairing (F := F) (ι := ι) z a)) • cosetKet xCode a := by sorry
