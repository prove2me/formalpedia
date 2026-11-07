-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_noSharedGenerator_regionUnion
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_regionUnion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:36:40.766529+00:00
-- url     : https://prove2.me/theorems/8e1a1b48-2c9a-459c-bbfa-7e930d9e36e4
-- title:
--   Local Stabilizer Hamiltonian: no Shared Generator region Union
-- statement:
--   Pairwise generator separation from a head region extends to the tail union.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L810-L821
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L810-L821

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_regionUnion
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    (R : Finset ι) (regions : List (Finset ι))
    (hseparated : ∀ T ∈ regions, H.NoSharedGenerator R T) :
    H.NoSharedGenerator R (regionUnion regions) := by sorry
