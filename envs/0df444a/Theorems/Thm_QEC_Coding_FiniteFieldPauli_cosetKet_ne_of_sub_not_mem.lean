-- Prove2me | Theorems.Thm_QEC_Coding_FiniteFieldPauli_cosetKet_ne_of_sub_not_mem
-- name    : QEC.Coding.FiniteFieldPauli.cosetKet_ne_of_sub_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:54:42.547191+00:00
-- url     : https://prove2.me/theorems/eb98dcd8-351d-4ffc-8d3b-a98e978150f5
-- title:
--   Finite Field Pauli: coset Ket ne of sub not mem
-- statement:
--   Different X-code cosets yield different physical indicator states.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1255-L1260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/FiniteFieldPauli.lean#L1255-L1260

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

theorem QEC.Coding.FiniteFieldPauli.cosetKet_ne_of_sub_not_mem (xCode : LinearCode F ι)
    (a b : Word F ι) (hnot : a - b ∉ xCode.carrier) :
    cosetKet xCode a ≠ cosetKet xCode b := by sorry
