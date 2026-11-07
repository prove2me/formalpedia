-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerProjector_mul_of_ne
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerProjector_mul_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:49:44.492886+00:00
-- url     : https://prove2.me/theorems/4362d10f-1bb4-478b-8cd7-9a9494dc6841
-- title:
--   Pauli Symplectic: joint Stabilizer Projector mul of ne
-- statement:
--   Different joint syndromes have zero product in the displayed order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L395-L449
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L395-L449

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerProjector_mul_of_ne
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndromeLeft syndromeRight : JointSyndrome κ) (hne : syndromeLeft ≠ syndromeRight) :
    jointStabilizerProjector checks hcomm syndromeLeft *
        jointStabilizerProjector checks hcomm syndromeRight = 0 := by sorry
