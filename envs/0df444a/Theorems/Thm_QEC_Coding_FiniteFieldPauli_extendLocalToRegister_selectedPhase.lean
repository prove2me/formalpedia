-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_extendLocalToRegister_selectedPhase
-- name    : QEC.Coding.FiniteFieldPauli.extendLocalToRegister_selectedPhase
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:56:34.883469+00:00
-- url     : https://prove2.me/theorems/01bd7bd3-de46-4092-b135-9aafd0e624e0
-- title:
--   Finite Field Pauli: extend Local To Register selected Phase
-- statement:
--   Extending the selected phase by identity gives the global field phase
--   after field-to-qudit relabelling whenever the word vanishes off the selected
--   region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1814-L1872
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1814-L1872

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
set_option maxRecDepth 4096

theorem QEC.Coding.FiniteFieldPauli.extendLocalToRegister_selectedPhase
    {ι' : Type u} [Fintype ι']
    (S : @Semantics.QuditSubsystem ι' inferInstance (Classical.decEq ι')
      (fun _ : ι' => Fintype.card F))
    (z : Word F ι') (hz : ∀ j, j ∉ S.selected → z j = 0) :
    S.extendLocalToRegister (selectedPhase S z) =
      (registerUnitary (F := F) (ι' := ι')).conjOperator (phase z) := by sorry
