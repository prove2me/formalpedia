-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_sum_jointStabilizerBornWeight_eq_one
-- name    : QEC.Coding.PauliSymplectic.sum_jointStabilizerBornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:51:10.903649+00:00
-- url     : https://prove2.me/theorems/ebdafaf4-6c0c-4bdc-94ef-f7c2c07bed72
-- title:
--   Pauli Symplectic: sum joint Stabilizer Born Weight eq one
-- statement:
--   The finite joint stabilizer Born weights sum to one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L720-L726
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L720-L726

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

theorem QEC.Coding.PauliSymplectic.sum_jointStabilizerBornWeight_eq_one
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    ∑ syndrome : JointSyndrome κ,
        (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho = 1 := by sorry
