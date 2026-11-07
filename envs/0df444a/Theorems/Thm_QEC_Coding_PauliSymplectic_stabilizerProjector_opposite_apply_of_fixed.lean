-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerProjector_opposite_apply_of_fixed
-- name    : QEC.Coding.PauliSymplectic.stabilizerProjector_opposite_apply_of_fixed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:44:29.844388+00:00
-- url     : https://prove2.me/theorems/df46440d-ac10-4616-bb9e-403d783d636e
-- title:
--   Pauli Symplectic: stabilizer Projector opposite apply of fixed
-- statement:
--   A vector in one eigenspace is annihilated by the opposite projector.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L173-L182
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L173-L182

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

theorem QEC.Coding.PauliSymplectic.stabilizerProjector_opposite_apply_of_fixed
    (P : Binary ι) (outcome : StabilizerOutcome)
    (ψ : Qubit.QubitRegister ι)
    (hfixed : stabilizerProjector P outcome ψ = ψ) :
    stabilizerProjector P outcome.opposite ψ = 0 := by sorry
