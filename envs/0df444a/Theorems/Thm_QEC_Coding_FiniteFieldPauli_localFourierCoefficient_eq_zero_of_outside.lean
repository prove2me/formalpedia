-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_localFourierCoefficient_eq_zero_of_outside
-- name    : QEC.Coding.FiniteFieldPauli.localFourierCoefficient_eq_zero_of_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:47:36.677509+00:00
-- url     : https://prove2.me/theorems/6db2fb48-3643-47b5-b815-3a8eded3d5e6
-- title:
--   Finite Field Pauli: local Fourier Coefficient eq zero of outside
-- statement:
--   Every Fourier mode of a tensor-local operator is supported inside its region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L711-L730
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L711-L730

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

theorem QEC.Coding.FiniteFieldPauli.localFourierCoefficient_eq_zero_of_outside
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x z : Word F ι')
    (houtside : (∃ j : ι', j ∉ S.selected ∧ x j ≠ 0) ∨
      (∃ j : ι', j ∉ S.selected ∧ z j ≠ 0)) :
    (wordCharacterBasis (F := F) (ι := ι')).repr
      (fun b => localMatrixDiagonal S E x b) z = 0 := by sorry
