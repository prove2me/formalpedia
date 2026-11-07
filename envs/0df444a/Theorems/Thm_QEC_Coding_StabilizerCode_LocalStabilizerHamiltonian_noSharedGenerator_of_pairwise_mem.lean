-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_noSharedGenerator_of_pairwise_mem
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_of_pairwise_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:36:29.805217+00:00
-- url     : https://prove2.me/theorems/38be19d1-f2c7-4b4d-972e-d61c73188d97
-- title:
--   Local Stabilizer Hamiltonian: no Shared Generator of pairwise mem
-- statement:
--   Pairwise generator separation relates any two distinct list members.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L658-L677
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L658-L677

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_of_pairwise_mem
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    {regions : List (Finset ι)}
    (hpairwise : regions.Pairwise H.NoSharedGenerator)
    {R T : Finset ι} (hR : R ∈ regions) (hT : T ∈ regions)
    (hRT : R ≠ T) :
    H.NoSharedGenerator R T := by sorry
