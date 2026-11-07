-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_sum_alternatingWidths
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.sum_alternatingWidths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:30:42.392568+00:00
-- url     : https://prove2.me/theorems/fad85d4f-cd1f-44ed-b13d-c02d7b84f47b
-- title:
--   Local Stabilizer Hamiltonian: sum alternating Widths
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the sum alternating Widths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L92-L94
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L92-L94

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.sum_alternatingWidths (a b r : Nat) :
    (alternatingWidths a b r).sum = a * (r - 1) + b * r := by sorry
