-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_noSharedGenerator_of_periodicIntervalSeparated
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_of_periodicIntervalSeparated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:34:21.449556+00:00
-- url     : https://prove2.me/theorems/bda2945a-1da4-4d49-a9bc-8b8c96fb76fb
-- title:
--   Local Stabilizer Hamiltonian: no Shared Generator of periodic Interval Separated
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the no Shared Generator of periodic Interval Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L633-L647
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L633-L647

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_of_periodicIntervalSeparated
    {L : Nat} {κ : Type*} [Fintype κ]
    (H : LocalStabilizerHamiltonian
      (ι := StripGeometry.Site L) (κ := κ))
    (r : Nat) (A B : Finset (StripGeometry.Site L))
    (hLocal : StripGeometry.HasPeriodicIntervalGeneratorSupport H r)
    (hSeparated : StripGeometry.PeriodicIntervalSeparated L r A B) :
    H.NoSharedGenerator A B := by sorry
