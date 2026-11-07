-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_matrixDiagonal_localOperator_translate_of_x_inside
-- name    : QEC.Coding.FiniteFieldPauli.matrixDiagonal_localOperator_translate_of_x_inside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:47:48.159729+00:00
-- url     : https://prove2.me/theorems/7f06793f-def2-4584-ad5a-7136083cd954
-- title:
--   Finite Field Pauli: matrix Diagonal local Operator translate of x inside
-- statement:
--   A local operator's matrix diagonal is unchanged by shifting input labels outside its region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L605-L641
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L605-L641

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

theorem QEC.Coding.FiniteFieldPauli.matrixDiagonal_localOperator_translate_of_x_inside
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x t b : Word F ι')
    (hx : ∀ j : ι', j ∉ S.selected → x j = 0)
    (ht : ∀ j : ι', j ∈ S.selected → t j = 0) :
    localMatrixDiagonal S E x (b + t) = localMatrixDiagonal S E x b := by sorry
