-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_not_detectable_pauli_of_logical
-- name    : QEC.Coding.FiniteFieldPauli.not_detectable_pauli_of_logical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:45:28.633036+00:00
-- url     : https://prove2.me/theorems/ae722adf-4b8e-43d9-b607-0ff796a30a72
-- title:
--   Finite Field Pauli: not detectable pauli of logical
-- statement:
--   Every nontrivial Pauli in the CSS normalizer is semantically nondetectable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1058-L1082
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1058-L1082

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

theorem QEC.Coding.FiniteFieldPauli.not_detectable_pauli_of_logical (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (x z : Word F ι)
    (hx : x ∈ zCode.dual.carrier) (hz : z ∈ xCode.dual.carrier)
    (hlogical : x ∉ xCode.carrier ∨ z ∉ zCode.carrier) :
    ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z) := by sorry
