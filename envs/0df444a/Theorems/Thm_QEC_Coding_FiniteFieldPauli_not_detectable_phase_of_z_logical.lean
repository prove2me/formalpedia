-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_not_detectable_phase_of_z_logical
-- name    : QEC.Coding.FiniteFieldPauli.not_detectable_phase_of_z_logical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:45.15646+00:00
-- url     : https://prove2.me/theorems/a3aa580f-66e2-46b0-a45f-fa6c80817c0f
-- title:
--   Finite Field Pauli: not detectable phase of z logical
-- statement:
--   A non-stabilizer Z-normalizer phase is a genuine semantic logical operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1026-L1055
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1026-L1055

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

theorem QEC.Coding.FiniteFieldPauli.not_detectable_phase_of_z_logical (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (z : Word F ι)
    (hz : z ∈ xCode.dual.carrier) (hznot : z ∉ zCode.carrier) :
    ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (phase z) := by sorry
