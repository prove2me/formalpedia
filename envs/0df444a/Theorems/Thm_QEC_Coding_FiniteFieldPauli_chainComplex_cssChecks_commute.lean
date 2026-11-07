-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_chainComplex_cssChecks_commute
-- name    : QEC.Coding.FiniteFieldPauli.chainComplex_cssChecks_commute
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:51:57.801691+00:00
-- url     : https://prove2.me/theorems/07181b25-b6d2-4094-b24c-cd5aa388de90
-- title:
--   Finite Field Pauli: chain Complex css Checks commute
-- statement:
--   Boundary-squared makes actual arbitrary-field CSS row checks commute.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L376-L385
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L376-L385

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

theorem QEC.Coding.FiniteFieldPauli.chainComplex_cssChecks_commute
    {κ₀ κ₂ : Type v} [Fintype κ₀] [Fintype κ₂]
    (K : ChainComplexData F (Word F κ₀) (Word F ι) (Word F κ₂))
    (x z : Word F ι)
    (hx : x ∈ K.firstCoboundaryCheckCode.carrier)
    (hz : z ∈ K.middleBoundaryCode.carrier) :
    shift x * phase z = phase z * shift x := by sorry
