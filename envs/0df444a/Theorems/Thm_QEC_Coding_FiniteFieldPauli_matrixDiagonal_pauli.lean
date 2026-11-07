-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_matrixDiagonal_pauli
-- name    : QEC.Coding.FiniteFieldPauli.matrixDiagonal_pauli
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:46:52.899846+00:00
-- url     : https://prove2.me/theorems/3d0abd24-0bc4-411f-8030-0b8e6f421539
-- title:
--   Finite Field Pauli: matrix Diagonal pauli
-- statement:
--   A Pauli occupies exactly one matrix displacement, with character entries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L545-L560
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L545-L560

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

theorem QEC.Coding.FiniteFieldPauli.matrixDiagonal_pauli (x x' z b : Word F ι) :
    matrixDiagonal (pauli x z) x' b =
      if x' = x then character F (wordPairing (F := F) (ι := ι) z b)
      else 0 := by sorry
