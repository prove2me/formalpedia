-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_pauliSupport_card_ge_of_not_detectable
-- name    : QEC.Coding.FiniteFieldPauli.pauliSupport_card_ge_of_not_detectable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-07T05:49:23.339726+00:00
-- url     : https://prove2.me/theorems/ff7706e0-cd00-4f38-ad40-b3b4b29a3549
-- title:
--   Finite Field Pauli: pauli Support card ge of not detectable
-- statement:
--   Algebraic CSS distance lower-bounds every nondetectable finite-field Pauli.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1162-L1186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1162-L1186

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

theorem QEC.Coding.FiniteFieldPauli.pauliSupport_card_ge_of_not_detectable
    [DecidableEq F] (xCode zCode : LinearCode F ι)
    (horth : xCode.carrier ≤ zCode.dual.carrier)
    (d : Nat) (hminimum : AlgebraicCSSMinimumDistance xCode zCode d)
    (x z : Word F ι)
    (hnot : ¬ Semantics.DetectableOn (cssQuantumCode xCode zCode) (pauli x z)) :
    d ≤ (pauliSupport x z).card := by sorry
