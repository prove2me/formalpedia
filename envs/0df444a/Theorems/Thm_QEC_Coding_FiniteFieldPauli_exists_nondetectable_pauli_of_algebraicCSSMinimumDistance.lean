-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_exists_nondetectable_pauli_of_algebraicCSSMinimumDistance
-- name    : QEC.Coding.FiniteFieldPauli.exists_nondetectable_pauli_of_algebraicCSSMinimumDistance
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:49:39.251807+00:00
-- url     : https://prove2.me/theorems/f8b62c6b-3cb6-43a8-96a0-2e3efde9e2f1
-- title:
--   Finite Field Pauli: exists nondetectable pauli of algebraic CSSMinimum Distance
-- statement:
--   The algebraic CSS minimum is attained by a nondetectable pure Pauli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1189-L1205
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1189-L1205

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

theorem QEC.Coding.FiniteFieldPauli.exists_nondetectable_pauli_of_algebraicCSSMinimumDistance
    [DecidableEq F] (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d) :
    ∃ x z : Word F ι,
      ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z) ∧
      (pauliSupport x z).card = d := by sorry
