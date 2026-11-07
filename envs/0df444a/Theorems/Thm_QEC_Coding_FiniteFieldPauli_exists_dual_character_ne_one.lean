-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_exists_dual_character_ne_one
-- name    : QEC.Coding.FiniteFieldPauli.exists_dual_character_ne_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:44:55.270186+00:00
-- url     : https://prove2.me/theorems/38fb319f-250a-492d-a25e-529f8c459230
-- title:
--   Finite Field Pauli: exists dual character ne one
-- statement:
--   A word outside a code has a dual-code witness with nontrivial character phase.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L76-L93
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L76-L93

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

theorem QEC.Coding.FiniteFieldPauli.exists_dual_character_ne_one (C : LinearCode F ι)
    (z : Word F ι) (hz : z ∉ C.carrier) :
    ∃ a : Word F ι, a ∈ C.dual.carrier ∧
      character F (wordPairing (F := F) (ι := ι) z a) ≠ 1 := by sorry
