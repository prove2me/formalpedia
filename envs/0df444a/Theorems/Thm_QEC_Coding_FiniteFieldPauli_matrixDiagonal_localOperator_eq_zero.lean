-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_matrixDiagonal_localOperator_eq_zero
-- name    : QEC.Coding.FiniteFieldPauli.matrixDiagonal_localOperator_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:13.717256+00:00
-- url     : https://prove2.me/theorems/00f6ada3-2e3e-42ea-ac52-a18239181d87
-- title:
--   Finite Field Pauli: matrix Diagonal local Operator eq zero
-- statement:
--   A tensor-local operator has no matrix displacement outside its selected sites.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L575-L592
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L575-L592

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
set_option maxHeartbeats 1000000

theorem QEC.Coding.FiniteFieldPauli.matrixDiagonal_localOperator_eq_zero
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x b : Word F ι')
    (houtside : ∃ j : ι', j ∉ S.selected ∧ x j ≠ 0) :
    matrixDiagonal (Semantics.FiniteAlphabet.localOperator S E) x b = 0 := by sorry
