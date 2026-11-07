-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_dual_dual_carrier_eq
-- name    : QEC.Coding.FiniteFieldPauli.dual_dual_carrier_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:45:05.577028+00:00
-- url     : https://prove2.me/theorems/ccdf1320-fae0-48bb-9559-ac8abe3510b6
-- title:
--   Finite Field Pauli: dual dual carrier eq
-- statement:
--   Finite-coordinate duality is involutive over every finite field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L63-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L63-L73

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

theorem QEC.Coding.FiniteFieldPauli.dual_dual_carrier_eq (C : LinearCode F ι) :
    C.dual.dual.carrier = C.carrier := by sorry
