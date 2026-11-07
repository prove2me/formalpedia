-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:51:31.948811+00:00
-- url     : https://prove2.me/theorems/760d81c6-9a01-4e9f-b0c0-1c54570b7662
-- title:
--   Pauli Symplectic: joint Stabilizer Branch Operator eq zero of born Weight eq zero
-- statement:
--   A zero joint-syndrome Born weight leaves an explicit zero raw branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L729-L735
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L729-L735

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ] [DecidableEq κ]

theorem QEC.Coding.PauliSymplectic.jointStabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι))
    (hzero : (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho = 0) :
    (jointStabilizerInstrument checks hcomm).branchOperator syndrome rho.toOperator = 0 := by sorry
