-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_extendLocalToRegister_selectedShift
-- name    : QEC.Coding.FiniteFieldPauli.extendLocalToRegister_selectedShift
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:56:18.515192+00:00
-- url     : https://prove2.me/theorems/68800554-a931-4a82-846a-844512e651a2
-- title:
--   Finite Field Pauli: extend Local To Register selected Shift
-- statement:
--   Extending the selected shift by identity gives the global field shift
--   after field-to-qudit relabelling whenever the word vanishes off the selected
--   region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1742-L1808
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1742-L1808

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

theorem QEC.Coding.FiniteFieldPauli.extendLocalToRegister_selectedShift
    {ι' : Type u} [Fintype ι']
    (S : @Semantics.QuditSubsystem ι' inferInstance (Classical.decEq ι')
      (fun _ : ι' => Fintype.card F))
    (x : Word F ι') (hx : ∀ j, j ∉ S.selected → x j = 0) :
    S.extendLocalToRegister (selectedShift S x) =
      (registerUnitary (F := F) (ι' := ι')).conjOperator (shift x) := by sorry
