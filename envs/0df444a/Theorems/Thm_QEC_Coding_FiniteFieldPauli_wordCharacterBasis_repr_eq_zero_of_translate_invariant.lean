-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_wordCharacterBasis_repr_eq_zero_of_translate_invariant
-- name    : QEC.Coding.FiniteFieldPauli.wordCharacterBasis_repr_eq_zero_of_translate_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:45:37.065587+00:00
-- url     : https://prove2.me/theorems/24e5ca57-b0a6-417d-86fd-3745d101157c
-- title:
--   Finite Field Pauli: word Character Basis repr eq zero of translate invariant
-- statement:
--   Translation invariance kills Fourier coefficients with nontrivial eigenphase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L164-L188
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L164-L188

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

theorem QEC.Coding.FiniteFieldPauli.wordCharacterBasis_repr_eq_zero_of_translate_invariant
    (f : Word F ι → Complex) (t z : Word F ι)
    (hinv : wordTranslate t f = f)
    (hchar : character F (wordPairing (F := F) (ι := ι) z t) ≠ 1) :
    (wordCharacterBasis (F := F) (ι := ι)).repr f z = 0 := by sorry
