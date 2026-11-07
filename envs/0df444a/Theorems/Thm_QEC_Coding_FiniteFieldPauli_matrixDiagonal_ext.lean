-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_matrixDiagonal_ext
-- name    : QEC.Coding.FiniteFieldPauli.matrixDiagonal_ext
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:47:23.144653+00:00
-- url     : https://prove2.me/theorems/82ec9782-bea0-4dc7-8b99-42295c59802d
-- title:
--   Finite Field Pauli: matrix Diagonal ext
-- statement:
--   Displacement-indexed matrix entries determine a finite register operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L563-L571
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L563-L571

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

theorem QEC.Coding.FiniteFieldPauli.matrixDiagonal_ext
    {E G : Semantics.Operator (Register F ι)}
    (h : ∀ x b : Word F ι, matrixDiagonal E x b = matrixDiagonal G x b) :
    E = G := by sorry
