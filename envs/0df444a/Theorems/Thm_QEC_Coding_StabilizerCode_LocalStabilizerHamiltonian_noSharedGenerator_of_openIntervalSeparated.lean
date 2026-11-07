-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_noSharedGenerator_of_openIntervalSeparated
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_of_openIntervalSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:34:51.594846+00:00
-- url     : https://prove2.me/theorems/98b0fded-b09a-4106-9dd7-349d8610b42b
-- title:
--   Local Stabilizer Hamiltonian: no Shared Generator of open Interval Separated
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the no Shared Generator of open Interval Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L617-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L617-L631

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_of_openIntervalSeparated
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (r : Nat) (A B : Finset (StripGeometry.Site L))
    (hLocal : StripGeometry.HasOpenIntervalGeneratorSupport H r)
    (hSeparated : StripGeometry.OpenIntervalSeparated L r A B) :
    H.NoSharedGenerator A B := by sorry
