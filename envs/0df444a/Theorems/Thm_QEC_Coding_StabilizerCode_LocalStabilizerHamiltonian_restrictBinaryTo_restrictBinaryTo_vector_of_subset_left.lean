-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_restrictBinaryTo_restrictBinaryTo_vector_of_subset_left
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.restrictBinaryTo_restrictBinaryTo_vector_of_subset_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:36:53.856111+00:00
-- url     : https://prove2.me/theorems/8873579c-6eca-4bbc-8606-751ea0b99df1
-- title:
--   Local Stabilizer Hamiltonian: restrict Binary To restrict Binary To vector of subset left
-- statement:
--   Restricting to a smaller region after a larger one preserves the smaller vector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L895-L909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L895-L909

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.restrictBinaryTo_restrictBinaryTo_vector_of_subset_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R S : Finset ι) (hRS : R ⊆ S) (E : Binary ι) :
    (Locality.restrictBinaryTo R (Locality.restrictBinaryTo S E)).vector =
      (Locality.restrictBinaryTo R E).vector := by sorry
