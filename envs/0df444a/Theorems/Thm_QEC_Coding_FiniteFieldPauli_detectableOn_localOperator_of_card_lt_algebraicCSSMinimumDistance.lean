-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_detectableOn_localOperator_of_card_lt_algebraicCSSMinimumDistance
-- name    : QEC.Coding.FiniteFieldPauli.detectableOn_localOperator_of_card_lt_algebraicCSSMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:49:28.590337+00:00
-- url     : https://prove2.me/theorems/90f5635e-e9ed-48c2-bda2-2d429d7a511c
-- title:
--   Finite Field Pauli: detectable On local Operator of card lt algebraic CSSMinimum Distance
-- statement:
--   Algebraic CSS distance detects every operator on fewer than `d` field-symbol sites.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1209-L1245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1209-L1245

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

theorem QEC.Coding.FiniteFieldPauli.detectableOn_localOperator_of_card_lt_algebraicCSSMinimumDistance
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d)
    (S : Semantics.QuditSubsystem (fun _ : ι' => Fintype.card F))
    (hcard : S.selected.card < d)
    (E : Semantics.Operator S.selectedSystem) :
    Semantics.DetectableOn (cssQuantumCode xCode zCode)
      (Semantics.FiniteAlphabet.localOperator S E) := by sorry
