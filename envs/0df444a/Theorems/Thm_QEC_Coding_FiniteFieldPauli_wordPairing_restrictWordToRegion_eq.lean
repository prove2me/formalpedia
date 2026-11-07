-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_wordPairing_restrictWordToRegion_eq
-- name    : QEC.Coding.FiniteFieldPauli.wordPairing_restrictWordToRegion_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:50:00.298176+00:00
-- url     : https://prove2.me/theorems/900cbca2-063b-40e4-9b69-9ea19f98a109
-- title:
--   Finite Field Pauli: word Pairing restrict Word To Region eq
-- statement:
--   Restricting both words preserves their pairing when the first word
--   vanishes outside the selected region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1644-L1665
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1644-L1665

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

theorem QEC.Coding.FiniteFieldPauli.wordPairing_restrictWordToRegion_eq
    {ι' : Type u} [Fintype ι'] [DecidableEq ι']
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (z a : Word F ι') (hz : ∀ j, j ∉ S.selected → z j = 0) :
    wordPairing (F := F) (ι := S.SelectedCoordinates)
        (restrictWordToRegion S z) (restrictWordToRegion S a) =
      wordPairing (F := F) (ι := ι') z a := by sorry
