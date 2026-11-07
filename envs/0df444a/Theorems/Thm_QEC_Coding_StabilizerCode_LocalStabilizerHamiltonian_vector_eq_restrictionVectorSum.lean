-- Prove2me | Theorems.Thm_QEC_Coding_StabilizerCode_LocalStabilizerHamiltonian_vector_eq_restrictionVectorSum
-- name    : QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.vector_eq_restrictionVectorSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T10:37:12.232747+00:00
-- url     : https://prove2.me/theorems/9e36b4af-1c10-4efd-8525-f80e6c05c8f2
-- title:
--   Local Stabilizer Hamiltonian: vector eq restriction Vector Sum
-- statement:
--   A Pauli supported on pairwise-disjoint regions is the sum of its restrictions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L936-L990
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/TwoDimensional/AlternatingStripDistance.lean#L936-L990

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

theorem QEC.Coding.StabilizerCode.LocalStabilizerHamiltonian.vector_eq_restrictionVectorSum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (regions : List (Finset ι))
    (hpairwise : regions.Pairwise Disjoint)
    (E : Binary ι) (hsupport : support E ⊆ regionUnion regions) :
    E.vector = restrictionVectorSum regions E := by sorry
