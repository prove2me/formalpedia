-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_hammingWeight_z_le_pauliSupport
-- name    : QEC.Coding.FiniteFieldPauli.hammingWeight_z_le_pauliSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:49:28.856196+00:00
-- url     : https://prove2.me/theorems/54b95102-7793-42cb-8f54-5be0aadd727d
-- title:
--   Finite Field Pauli: hamming Weight z le pauli Support
-- statement:
--   A Pauli's Z word weight is bounded by its total coordinate support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1156-L1159
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1156-L1159

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
omit [Fintype F]

theorem QEC.Coding.FiniteFieldPauli.hammingWeight_z_le_pauliSupport [DecidableEq F]
    (x z : Word F ι) :
    HammingWeight z ≤ (pauliSupport x z).card := by sorry
