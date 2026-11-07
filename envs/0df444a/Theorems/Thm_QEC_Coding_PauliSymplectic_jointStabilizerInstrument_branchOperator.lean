-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_branchOperator
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerInstrument_branchOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:50:46.753206+00:00
-- url     : https://prove2.me/theorems/b30b392e-e9c4-4fa8-bf06-5c3f47e0b14d
-- title:
--   Pauli Symplectic: joint Stabilizer Instrument branch Operator
-- statement:
--   A joint syndrome branch is literal nondestructive joint-projector compression.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L699-L710
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L699-L710

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerInstrument_branchOperator
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (A : Operator (Qubit.QubitRegister ι)) :
    (jointStabilizerInstrument checks hcomm).branchOperator syndrome A =
      jointStabilizerProjector checks hcomm syndrome * A *
        jointStabilizerProjector checks hcomm syndrome := by sorry
