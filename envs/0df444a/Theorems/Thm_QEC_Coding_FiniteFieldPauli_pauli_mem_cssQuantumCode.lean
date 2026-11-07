-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_pauli_mem_cssQuantumCode
-- name    : QEC.Coding.FiniteFieldPauli.pauli_mem_cssQuantumCode
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:44:46.229691+00:00
-- url     : https://prove2.me/theorems/5523814b-b331-4a2d-af90-8b8648347d69
-- title:
--   Finite Field Pauli: pauli mem css Quantum Code
-- statement:
--   Paulis in both CSS normalizer sectors preserve the actual code subspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L884-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L884-L909

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

theorem QEC.Coding.FiniteFieldPauli.pauli_mem_cssQuantumCode (xCode zCode : LinearCode F ι)
    (x z : Word F ι)
    (hx : x ∈ zCode.dual.carrier)
    (hz : z ∈ xCode.dual.carrier)
    (ψ : Register F ι)
    (hψ : ψ ∈ (cssQuantumCode xCode zCode).carrier) :
    pauli x z ψ ∈ (cssQuantumCode xCode zCode).carrier := by sorry
