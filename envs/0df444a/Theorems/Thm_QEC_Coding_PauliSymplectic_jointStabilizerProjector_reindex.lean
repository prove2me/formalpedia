-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_reindex
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerProjector_reindex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:51:47.659197+00:00
-- url     : https://prove2.me/theorems/33a538d9-05dd-473e-bd14-f44090e0276a
-- title:
--   Pauli Symplectic: joint Stabilizer Projector reindex
-- statement:
--   Reindexing a finite check family along an equivalence leaves its joint projector unchanged.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L788-L812
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L788-L812

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerProjector_reindex
    {κ' : Type v} [Fintype κ'] [DecidableEq κ']
    (equiv : κ ≃ κ') (checks : κ → Binary ι)
    (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    jointStabilizerProjector checks hcomm syndrome =
      jointStabilizerProjector
        (fun check' => checks (equiv.symm check'))
        (fun left right => hcomm (equiv.symm left) (equiv.symm right))
        (fun check' => syndrome (equiv.symm check')) := by sorry
