-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuditCode_not_noInformationOn_fullRegion
-- name    : QEC.Coding.FiniteFieldPauli.cssQuditCode_not_noInformationOn_fullRegion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:50:45.942701+00:00
-- url     : https://prove2.me/theorems/4477995e-ba48-4b35-a3e5-30cb1ece7bf7
-- title:
--   Finite Field Pauli: css Qudit Code not no Information On full Region
-- statement:
--   A nontrivial CSS logical Pauli makes the full qudit region informative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1930-L1963
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1930-L1963

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

theorem QEC.Coding.FiniteFieldPauli.cssQuditCode_not_noInformationOn_fullRegion
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    ¬ Semantics.QuditSubsystem.NoInformationOn (cssQuditCode xCode zCode)
      (Semantics.QuditSubsystem.fullRegion (fun _ : ι' => Fintype.card F)) := by sorry
