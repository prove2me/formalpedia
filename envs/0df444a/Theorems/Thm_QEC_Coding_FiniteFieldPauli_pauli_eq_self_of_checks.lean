-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_pauli_eq_self_of_checks
-- name    : QEC.Coding.FiniteFieldPauli.pauli_eq_self_of_checks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:58.112545+00:00
-- url     : https://prove2.me/theorems/2c5eea57-be88-4cd0-aa15-f1860c888442
-- title:
--   Finite Field Pauli: pauli eq self of checks
-- statement:
--   Products of X and Z stabilizers act as the identity on the CSS carrier.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L912-L918
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L912-L918

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

theorem QEC.Coding.FiniteFieldPauli.pauli_eq_self_of_checks (xCode zCode : LinearCode F ι)
    (x z : Word F ι)
    (hx : x ∈ xCode.carrier) (hz : z ∈ zCode.carrier)
    (ψ : Register F ι) (hψ : ψ ∈ (cssQuantumCode xCode zCode).carrier) :
    pauli x z ψ = ψ := by sorry
