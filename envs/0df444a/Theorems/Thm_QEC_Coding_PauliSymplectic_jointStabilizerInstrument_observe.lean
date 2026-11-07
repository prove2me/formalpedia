-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_observe
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:49:34.763768+00:00
-- url     : https://prove2.me/theorems/78f29376-320f-4992-92f3-996b35c581a5
-- title:
--   Pauli Symplectic: joint Stabilizer Instrument observe
-- statement:
--   The Pauli Symplectic construction uses the joint Stabilizer Instrument observe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L692-L696
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L692-L696

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) :
    (jointStabilizerInstrument checks hcomm).observe syndrome = syndrome := by sorry

attribute [defeq] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_observe
