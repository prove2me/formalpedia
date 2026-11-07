-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_algebraicCSSMinimumDistance_le_semanticQuditDistance
-- name    : QEC.Coding.FiniteFieldPauli.algebraicCSSMinimumDistance_le_semanticQuditDistance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:57:17.734416+00:00
-- url     : https://prove2.me/theorems/0f36bfe9-dabb-4e33-b0ce-98861df0fa03
-- title:
--   Finite Field Pauli: algebraic CSSMinimum Distance le semantic Qudit Distance
-- statement:
--   Algebraic CSS distance lower-bounds the semantic distance used by qLDPC families.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1967-L1979
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1967-L1979

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

theorem QEC.Coding.FiniteFieldPauli.algebraicCSSMinimumDistance_le_semanticQuditDistance
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    d ≤ QLDPC.semanticQuditDistance (fun _ : ι' => Fintype.card F)
      (cssQuditCode xCode zCode) := by sorry
