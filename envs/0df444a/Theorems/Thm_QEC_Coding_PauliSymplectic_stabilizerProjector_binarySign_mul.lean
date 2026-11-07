-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerProjector_binarySign_mul
-- name    : QEC.Coding.PauliSymplectic.stabilizerProjector_binarySign_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:44:36.64958+00:00
-- url     : https://prove2.me/theorems/a48d297f-043c-44e7-b43f-32d573daaa74
-- title:
--   Pauli Symplectic: stabilizer Projector binary Sign mul
-- statement:
--   Changing the stored global Pauli sign visibly swaps the two outcomes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L185-L193
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L185-L193

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

theorem QEC.Coding.PauliSymplectic.stabilizerProjector_binarySign_mul
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector (binaryMul (binarySign (1 : ZMod 2)) P) outcome =
      stabilizerProjector P outcome.opposite := by sorry
