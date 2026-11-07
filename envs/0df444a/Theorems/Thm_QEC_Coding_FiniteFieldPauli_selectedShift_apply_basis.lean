-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_selectedShift_apply_basis
-- name    : QEC.Coding.FiniteFieldPauli.selectedShift_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:49:58.784581+00:00
-- url     : https://prove2.me/theorems/7d3811b3-bb59-4db0-92de-64859df2d6a8
-- title:
--   Finite Field Pauli: selected Shift apply basis
-- statement:
--   The selected shift translates the relabelled selected-coordinate basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1691-L1717
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1691-L1717

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

theorem QEC.Coding.FiniteFieldPauli.selectedShift_apply_basis
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (x : Word F ι') (a : Word F S.SelectedCoordinates) :
    selectedShift S x
        (EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) a)) =
      EuclideanSpace.basisFun _ Complex
        (fieldLabelEquiv (F := F) (a - restrictWordToRegion S x)) := by sorry
