-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerInstrument_kraus
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:49:46.406889+00:00
-- url     : https://prove2.me/theorems/f0b18252-7a26-4410-935d-27365d222d7d
-- title:
--   Pauli Symplectic: joint Stabilizer Instrument kraus
-- statement:
--   The Pauli Symplectic construction uses the joint Stabilizer Instrument kraus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L685-L689
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L685-L689

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right)) :
    (jointStabilizerInstrument checks hcomm).kraus =
      jointStabilizerKrausFamily checks hcomm := by sorry

attribute [defeq] QEC.Coding.PauliSymplectic.jointStabilizerInstrument_kraus
