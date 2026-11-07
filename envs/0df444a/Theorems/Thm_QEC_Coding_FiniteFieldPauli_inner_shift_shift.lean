-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_inner_shift_shift
-- name    : QEC.Coding.FiniteFieldPauli.inner_shift_shift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:03.576194+00:00
-- url     : https://prove2.me/theorems/b812e0f6-2784-46a2-b19e-d079533117dc
-- title:
--   Finite Field Pauli: inner shift shift
-- statement:
--   Translation of computational labels preserves the register inner product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L800-L804
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L800-L804

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

theorem QEC.Coding.FiniteFieldPauli.inner_shift_shift (t : Word F ι) (u v : Register F ι) :
    inner Complex (shift t u) (shift t v) = inner Complex u v := by sorry
