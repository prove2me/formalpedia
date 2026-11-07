-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerProjector_fixed_iff
-- name    : QEC.Coding.PauliSymplectic.stabilizerProjector_fixed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:38.483244+00:00
-- url     : https://prove2.me/theorems/54cc5645-328b-4bbf-b534-ebc5c9924983
-- title:
--   Pauli Symplectic: stabilizer Projector fixed iff
-- statement:
--   Projector fixed points are exactly the corresponding signed eigenspace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L137-L170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L137-L170

import Definitions.Def_QEC_Coding_Stabilizer_HermitianPauli
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Coding_Stabilizer_Measurement
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.PauliSymplectic
open Semantics
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

theorem QEC.Coding.PauliSymplectic.stabilizerProjector_fixed_iff
    (P : Binary ι) (outcome : StabilizerOutcome)
    (ψ : Qubit.QubitRegister ι) :
    stabilizerProjector P outcome ψ = ψ ↔
      toHermitianQubitOperator P ψ = outcome.sign • ψ := by sorry
