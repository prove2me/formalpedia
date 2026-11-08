-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_cosetKet_mul_eq_zero_of_sub_not_mem
-- name    : QEC.Coding.FiniteFieldPauli.cosetKet_mul_eq_zero_of_sub_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:55:03.892118+00:00
-- url     : https://prove2.me/theorems/d5b89f92-dc5a-4971-9624-b5d56fbfe30f
-- title:
--   Finite Field Pauli: coset Ket mul eq zero of sub not mem
-- statement:
--   Distinct X-code cosets have disjoint computational-basis support.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1263-L1274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1263-L1274

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

theorem QEC.Coding.FiniteFieldPauli.cosetKet_mul_eq_zero_of_sub_not_mem (xCode : LinearCode F ι)
    (a b η : Word F ι) (hnot : a - b ∉ xCode.carrier) :
    cosetKet xCode a η * cosetKet xCode b η = 0 := by sorry
