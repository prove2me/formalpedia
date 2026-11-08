-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_cssQuditCode_bptMeasurementDistance_of_algebraicCSSMinimumDistance
-- name    : QEC.Coding.FiniteFieldPauli.cssQuditCode_bptMeasurementDistance_of_algebraicCSSMinimumDistance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:50:09.702757+00:00
-- url     : https://prove2.me/theorems/a80a9cad-8fe1-4919-a6b9-425c0a8de76a
-- title:
--   Finite Field Pauli: css Qudit Code bpt Measurement Distance of algebraic CSSMinimum Distance
-- statement:
--   Algebraic CSS minimum distance implies the semantic BPT measurement-distance bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1911-L1926
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1911-L1926

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

theorem QEC.Coding.FiniteFieldPauli.cssQuditCode_bptMeasurementDistance_of_algebraicCSSMinimumDistance
    {ι' : Type u} [Fintype ι']
    (xCode zCode : LinearCode F ι')
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    Semantics.QuditSubsystem.BPTMeasurementDistance
      (cssQuditCode xCode zCode) d := by sorry
