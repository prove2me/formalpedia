-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_wordTranslate_wordCharacterBasis
-- name    : QEC.Coding.FiniteFieldPauli.wordTranslate_wordCharacterBasis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:45:50.481292+00:00
-- url     : https://prove2.me/theorems/b150e95d-26e4-4bef-a637-279c800137c4
-- title:
--   Finite Field Pauli: word Translate word Character Basis
-- statement:
--   Every pairing character is an eigenfunction of word translation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L152-L161
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L152-L161

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

theorem QEC.Coding.FiniteFieldPauli.wordTranslate_wordCharacterBasis (t z : Word F ι) :
    wordTranslate t (wordCharacterBasis (F := F) (ι := ι) z) =
      (character F (wordPairing (F := F) (ι := ι) z t)) •
        wordCharacterBasis (F := F) (ι := ι) z := by sorry
