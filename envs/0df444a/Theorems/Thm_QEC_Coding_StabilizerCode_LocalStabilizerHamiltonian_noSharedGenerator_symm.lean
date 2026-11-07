-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_noSharedGenerator_symm
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:33:13.037686+00:00
-- url     : https://prove2.me/theorems/5be50cdf-4ab1-49bf-80b7-44ab26e92529
-- title:
--   Local Stabilizer Hamiltonian: no Shared Generator symm
-- statement:
--   The Local Stabilizer Hamiltonian construction uses the no Shared Generator symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L649-L655
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L649-L655

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.noSharedGenerator_symm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (H : LocalStabilizerHamiltonian (ι := ι) (κ := κ))
    {R T : Finset ι} (h : H.NoSharedGenerator R T) :
    H.NoSharedGenerator T R := by sorry
