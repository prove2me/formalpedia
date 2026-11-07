-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_phase_basis
-- name    : QEC.Coding.FiniteFieldPauli.phase_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:10.041488+00:00
-- url     : https://prove2.me/theorems/074cf398-7a62-43bc-972e-396d1002618b
-- title:
--   Finite Field Pauli: phase basis
-- statement:
--   A phase acts diagonally on computational basis kets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L247-L257
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L247-L257

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

theorem QEC.Coding.FiniteFieldPauli.phase_basis (z a : Word F ι) :
    phase z (EuclideanSpace.basisFun (Word F ι) Complex a) =
      (character F (wordPairing (F := F) (ι := ι) z a)) •
        EuclideanSpace.basisFun (Word F ι) Complex a := by sorry
