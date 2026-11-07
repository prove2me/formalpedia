-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_fixed_iff
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerProjector_fixed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:50:42.348107+00:00
-- url     : https://prove2.me/theorems/be944b68-c52a-414e-8fcf-64a6cd088211
-- title:
--   Pauli Symplectic: joint Stabilizer Projector fixed iff
-- statement:
--   The joint projector fixes exactly the simultaneous signed eigenspace of the
--   commuting Hermitian binary checks.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L339-L362
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L339-L362

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerProjector_fixed_iff
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (psi : Qubit.QubitRegister ι) :
    jointStabilizerProjector checks hcomm syndrome psi = psi ↔
      ∀ check, toHermitianQubitOperator (checks check) psi =
        (syndrome check).sign • psi := by sorry
