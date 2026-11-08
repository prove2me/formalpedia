-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_pauliFourierCoefficient_localOperator_eq_zero_of_support_not_subset
-- name    : QEC.Coding.FiniteFieldPauli.pauliFourierCoefficient_localOperator_eq_zero_of_support_not_subset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:49:52.262655+00:00
-- url     : https://prove2.me/theorems/1a953430-6ede-4489-868c-075a71dade2f
-- title:
--   Finite Field Pauli: pauli Fourier Coefficient local Operator eq zero of support not subset
-- statement:
--   A tensor-local operator has no Pauli coefficient whose support leaves the region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1138-L1145
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1138-L1145

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
set_option maxHeartbeats 1000000

theorem QEC.Coding.FiniteFieldPauli.pauliFourierCoefficient_localOperator_eq_zero_of_support_not_subset
    {ι' : Type u} [Fintype ι'] [DecidableEq ι'] [DecidableEq F]
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (E : Semantics.Operator S.selectedSystem)
    (x z : Word F ι') (houtside : ¬ pauliSupport x z ⊆ S.selected) :
    pauliFourierCoefficient (Semantics.FiniteAlphabet.localOperator S E) x z = 0 := by sorry
