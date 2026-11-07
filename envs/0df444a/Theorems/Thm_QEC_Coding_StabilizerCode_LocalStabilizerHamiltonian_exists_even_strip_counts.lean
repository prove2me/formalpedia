-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_exists_even_strip_counts
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_even_strip_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:35:21.841799+00:00
-- url     : https://prove2.me/theorems/a7381f9d-df02-400e-8f3b-bddd9e9d774b
-- title:
--   Local Stabilizer Hamiltonian: exists even strip counts
-- statement:
--   The arithmetic core of the BT09 alternating-strip construction: above the
--   source threshold, `L` is a sum of an even number of widths, each equal to
--   `r - 1` or `r`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L26-L69
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L26-L69

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.exists_even_strip_counts
    {L r : Nat} (hr : 2 ≤ r) (hL : 2 * (r - 1) ^ 2 ≤ L) :
    ∃ a b : Nat, L = a * (r - 1) + b * r ∧ Even (a + b) := by sorry
