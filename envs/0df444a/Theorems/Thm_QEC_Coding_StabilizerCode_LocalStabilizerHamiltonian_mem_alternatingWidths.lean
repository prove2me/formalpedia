-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_mem_alternatingWidths
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_alternatingWidths
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:31.600775+00:00
-- url     : https://prove2.me/theorems/defed0b1-1be4-46df-9aba-7e3d3615b7fa
-- title:
--   Local Stabilizer Hamiltonian: mem alternating Widths
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the mem alternating Widths property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L96-L102
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L96-L102

import Definitions.Def_QEC_Coding_Stabilizer_Cleaning
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Coding_Stabilizer_TwoDimensional_AlternatingStripDistance
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.StabilizerCode
open QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian
open PauliSymplectic

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.mem_alternatingWidths
    {a b r w : Nat} (hw : w ∈ alternatingWidths a b r) :
    w = r - 1 ∨ w = r := by sorry
