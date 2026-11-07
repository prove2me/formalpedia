-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_detectable_pauli_of_x_not_dual
-- name    : QEC.Coding.FiniteFieldPauli.detectable_pauli_of_x_not_dual
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:33.956514+00:00
-- url     : https://prove2.me/theorems/c7f2352f-0d19-43db-ab8e-cb51ad3057aa
-- title:
--   Finite Field Pauli: detectable pauli of x not dual
-- statement:
--   An X shift outside the Z-check normalizer has zero compression on the code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L921-L944
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L921-L944

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

theorem QEC.Coding.FiniteFieldPauli.detectable_pauli_of_x_not_dual (xCode zCode : LinearCode F ι)
    (x z : Word F ι) (hx : x ∉ zCode.dual.carrier) :
    Semantics.DetectableOnWithScalar
      (cssQuantumCode xCode zCode) (pauli x z) 0 := by sorry
