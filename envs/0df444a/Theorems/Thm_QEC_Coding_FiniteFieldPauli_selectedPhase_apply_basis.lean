-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_selectedPhase_apply_basis
-- name    : QEC.Coding.FiniteFieldPauli.selectedPhase_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:50:16.658187+00:00
-- url     : https://prove2.me/theorems/a56947ed-8241-4644-b853-f57e339862bb
-- title:
--   Finite Field Pauli: selected Phase apply basis
-- statement:
--   The selected phase is diagonal in the relabelled selected-coordinate basis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1720-L1736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1720-L1736

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

theorem QEC.Coding.FiniteFieldPauli.selectedPhase_apply_basis
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (z : Word F ι') (a : Word F S.SelectedCoordinates) :
    selectedPhase S z
        (EuclideanSpace.basisFun _ Complex
          (fieldLabelEquiv (F := F) a)) =
      (character F (wordPairing (F := F) (ι := S.SelectedCoordinates)
        (restrictWordToRegion S z) a)) •
        EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a) := by sorry
