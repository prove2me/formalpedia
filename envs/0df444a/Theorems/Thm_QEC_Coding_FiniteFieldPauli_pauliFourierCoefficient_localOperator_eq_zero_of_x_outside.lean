-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_pauliFourierCoefficient_localOperator_eq_zero_of_x_outside
-- name    : QEC.Coding.FiniteFieldPauli.pauliFourierCoefficient_localOperator_eq_zero_of_x_outside
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:48:38.258375+00:00
-- url     : https://prove2.me/theorems/fd1c70de-643e-42e8-b67a-1b7267d8f86a
-- title:
--   Finite Field Pauli: pauli Fourier Coefficient local Operator eq zero of x outside
-- statement:
--   Tensor-local operators have no Pauli Fourier displacement outside the region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L692-L707
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L692-L707

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

theorem QEC.Coding.FiniteFieldPauli.pauliFourierCoefficient_localOperator_eq_zero_of_x_outside
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x z : Word F ι')
    (houtside : ∃ j : ι', j ∉ S.selected ∧ x j ≠ 0) :
    (wordCharacterBasis (F := F) (ι := ι')).repr
      (fun b => matrixDiagonal (Semantics.FiniteAlphabet.localOperator S E) x b) z = 0 := by sorry
