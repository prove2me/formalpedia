-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuantumCode_carrier_ne_bot
-- name    : QEC.Coding.FiniteFieldPauli.cssQuantumCode_carrier_ne_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:55:31.370488+00:00
-- url     : https://prove2.me/theorems/dc4b784b-20ec-4cf8-b035-9f6417805740
-- title:
--   Finite Field Pauli: css Quantum Code carrier ne bot
-- statement:
--   An orthogonal CSS pair has a genuinely nonzero semantic codespace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1566-L1573
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1566-L1573

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

theorem QEC.Coding.FiniteFieldPauli.cssQuantumCode_carrier_ne_bot (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (cssQuantumCode xCode zCode).carrier ≠ ⊥ := by sorry
