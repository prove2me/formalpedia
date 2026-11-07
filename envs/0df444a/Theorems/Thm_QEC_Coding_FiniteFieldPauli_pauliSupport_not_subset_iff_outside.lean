-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_pauliSupport_not_subset_iff_outside
-- name    : QEC.Coding.FiniteFieldPauli.pauliSupport_not_subset_iff_outside
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:48:47.766345+00:00
-- url     : https://prove2.me/theorems/2e178552-9db1-4719-908c-f17e9cfa4780
-- title:
--   Finite Field Pauli: pauli Support not subset iff outside
-- statement:
--   If a Pauli support escapes a region, some X or Z coordinate escapes it.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1120-L1134
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1120-L1134

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
omit [Fintype F]

theorem QEC.Coding.FiniteFieldPauli.pauliSupport_not_subset_iff_outside [DecidableEq F]
    (x z : Word F ι) (S : Finset ι) :
    ¬ pauliSupport x z ⊆ S ↔
      (∃ j : ι, j ∉ S ∧ x j ≠ 0) ∨
        (∃ j : ι, j ∉ S ∧ z j ≠ 0) := by sorry
