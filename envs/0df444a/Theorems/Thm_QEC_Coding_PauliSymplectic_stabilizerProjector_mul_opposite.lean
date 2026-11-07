-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerProjector_mul_opposite
-- name    : QEC.Coding.PauliSymplectic.stabilizerProjector_mul_opposite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:29.065584+00:00
-- url     : https://prove2.me/theorems/5e60c595-efbe-49a6-9f32-80fb549a0de6
-- title:
--   Pauli Symplectic: stabilizer Projector mul opposite
-- statement:
--   Opposite spectral projectors are orthogonal in the displayed order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L108-L117
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L108-L117

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

theorem QEC.Coding.PauliSymplectic.stabilizerProjector_mul_opposite
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome *
        stabilizerProjector P outcome.opposite = 0 := by sorry
