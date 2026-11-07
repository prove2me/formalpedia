-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuantumCode_dimension_eq_card_cosets
-- name    : QEC.Coding.FiniteFieldPauli.cssQuantumCode_dimension_eq_card_cosets
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:49:19.681206+00:00
-- url     : https://prove2.me/theorems/94d5a8e9-2068-49df-b45d-479141fdf1c5
-- title:
--   Finite Field Pauli: css Quantum Code dimension eq card cosets
-- statement:
--   The physical CSS codespace dimension is the number of admissible cosets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1453-L1457
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1453-L1457

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

theorem QEC.Coding.FiniteFieldPauli.cssQuantumCode_dimension_eq_card_cosets (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier) :
    (cssQuantumCode xCode zCode).dimension =
      Fintype.card (AdmissibleCoset xCode zCode) := by sorry
