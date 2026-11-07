-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_eigen
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerProjector_eigen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:50:07.909551+00:00
-- url     : https://prove2.me/theorems/6b1178e0-6167-45ea-bf10-1796fbd20f44
-- title:
--   Pauli Symplectic: joint Stabilizer Projector eigen
-- statement:
--   Each check acts on its joint spectral projector by the selected eigenvalue.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L289-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L289-L316

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerProjector_eigen
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (check : κ) :
    toHermitianQubitOperator (checks check) *
        jointStabilizerProjector checks hcomm syndrome =
      (syndrome check).sign • jointStabilizerProjector checks hcomm syndrome := by sorry
