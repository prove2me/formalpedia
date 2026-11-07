-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_opposite_stabilizerProjector_mul
-- name    : QEC.Coding.PauliSymplectic.opposite_stabilizerProjector_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:44:25.941507+00:00
-- url     : https://prove2.me/theorems/52353cff-c483-4836-bf07-2ad37a2e0e79
-- title:
--   Pauli Symplectic: opposite stabilizer Projector mul
-- statement:
--   Opposite spectral projectors are orthogonal in the reverse order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L120-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L120-L124

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

theorem QEC.Coding.PauliSymplectic.opposite_stabilizerProjector_mul
    (P : Binary ι) (outcome : StabilizerOutcome) :
    stabilizerProjector P outcome.opposite *
        stabilizerProjector P outcome = 0 := by sorry
