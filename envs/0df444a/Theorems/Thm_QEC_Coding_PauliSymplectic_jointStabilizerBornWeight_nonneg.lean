-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerBornWeight_nonneg
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerBornWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:51:27.367767+00:00
-- url     : https://prove2.me/theorems/0895b304-fd70-43c8-a8a5-67884126b02f
-- title:
--   Pauli Symplectic: joint Stabilizer Born Weight nonneg
-- statement:
--   Joint stabilizer Born weights are nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L713-L717
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L713-L717

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerBornWeight_nonneg
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι)) :
    0 ≤ (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho := by sorry
