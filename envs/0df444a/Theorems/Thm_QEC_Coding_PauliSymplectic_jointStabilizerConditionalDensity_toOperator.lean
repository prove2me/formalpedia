-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_jointStabilizerConditionalDensity_toOperator
-- name    : QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:49:54.394492+00:00
-- url     : https://prove2.me/theorems/9fcdfd0e-6543-445f-8623-a230e7204d40
-- title:
--   Pauli Symplectic: joint Stabilizer Conditional Density to Operator
-- statement:
--   The Pauli Symplectic construction uses the joint Stabilizer Conditional Density to Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L746-L756
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L746-L756

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

theorem QEC.Coding.PauliSymplectic.jointStabilizerConditionalDensity_toOperator
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (syndrome : JointSyndrome κ) (rho : DensityOperator (Qubit.QubitRegister ι))
    (hpos : 0 < (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho) :
    (jointStabilizerConditionalDensity checks hcomm syndrome rho hpos).toOperator =
      (((jointStabilizerInstrument checks hcomm).bornWeight syndrome rho : Complex)⁻¹) •
        (jointStabilizerProjector checks hcomm syndrome * rho.toOperator *
          jointStabilizerProjector checks hcomm syndrome) := by sorry
