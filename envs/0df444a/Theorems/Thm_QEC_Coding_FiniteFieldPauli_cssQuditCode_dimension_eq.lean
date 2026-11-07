-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuditCode_dimension_eq
-- name    : QEC.Coding.FiniteFieldPauli.cssQuditCode_dimension_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:51:06.080458+00:00
-- url     : https://prove2.me/theorems/2b9417e6-596e-4b0d-84f4-6297c6f588b6
-- title:
--   Finite Field Pauli: css Qudit Code dimension eq
-- statement:
--   The explicit field-to-qudit relabelling preserves the actual codespace dimension.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1982-L1987
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1982-L1987

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

theorem QEC.Coding.FiniteFieldPauli.cssQuditCode_dimension_eq {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι') :
    (cssQuditCode xCode zCode).dimension =
      (cssQuantumCode xCode zCode).dimension := by sorry
