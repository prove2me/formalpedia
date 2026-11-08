-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_detectable_pauli_iff
-- name    : QEC.Coding.FiniteFieldPauli.detectable_pauli_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:55.535191+00:00
-- url     : https://prove2.me/theorems/49e5d873-a84c-400d-a717-12611cc07f81
-- title:
--   Finite Field Pauli: detectable pauli iff
-- statement:
--   Exact semantic detectability criterion for arbitrary finite-field CSS Paulis.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1085-L1111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1085-L1111

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

theorem QEC.Coding.FiniteFieldPauli.detectable_pauli_iff (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (x z : Word F ι) :
    Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z) ↔
      x ∉ zCode.dual.carrier ∨ z ∉ xCode.dual.carrier ∨
        (x ∈ xCode.carrier ∧ z ∈ zCode.carrier) := by sorry
