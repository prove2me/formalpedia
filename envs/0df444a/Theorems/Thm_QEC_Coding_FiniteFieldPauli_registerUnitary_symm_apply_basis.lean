-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_registerUnitary_symm_apply_basis
-- name    : QEC.Coding.FiniteFieldPauli.registerUnitary_symm_apply_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:45:29.401205+00:00
-- url     : https://prove2.me/theorems/cec94a33-4a6b-44d6-a915-a33ab84e0049
-- title:
--   Finite Field Pauli: register Unitary symm apply basis
-- statement:
--   Inverse relabelling sends a standard basis ket back to its field label.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1597-L1606
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1597-L1606

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

theorem QEC.Coding.FiniteFieldPauli.registerUnitary_symm_apply_basis
    {ι' : Type u} [Fintype ι'] (a : Word F ι') :
    (registerUnitary (F := F) (ι' := ι')).symm
        (EuclideanSpace.basisFun _ Complex (fieldLabelEquiv (F := F) a)) =
      EuclideanSpace.basisFun _ Complex a := by sorry
