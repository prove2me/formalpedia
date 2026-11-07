-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
-- name    : QEC.Coding.PauliSymplectic.stabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:44:50.743482+00:00
-- url     : https://prove2.me/theorems/8ab28158-7df3-4d57-95f4-00c1351dc7dc
-- title:
--   Pauli Symplectic: stabilizer Branch Operator eq zero of born Weight eq zero
-- statement:
--   A zero stabilizer Born weight leaves an explicit zero raw branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L271-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L271-L277

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.stabilizerBranchOperator_eq_zero_of_bornWeight_eq_zero
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι))
    (hzero : (stabilizerInstrument P).bornWeight outcome rho = 0) :
    (stabilizerInstrument P).branchOperator outcome rho.toOperator = 0 := by sorry
