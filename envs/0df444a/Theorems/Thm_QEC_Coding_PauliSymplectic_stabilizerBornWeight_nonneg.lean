-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_stabilizerBornWeight_nonneg
-- name    : QEC.Coding.PauliSymplectic.stabilizerBornWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:02.383223+00:00
-- url     : https://prove2.me/theorems/19820522-ebf6-48d1-b3bc-f5d21f5fbb10
-- title:
--   Pauli Symplectic: stabilizer Born Weight nonneg
-- statement:
--   Binary stabilizer Born weights are nonnegative.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L255-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L255-L259

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

theorem QEC.Coding.PauliSymplectic.stabilizerBornWeight_nonneg
    (P : Binary ι) (outcome : StabilizerOutcome)
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    0 ≤ (stabilizerInstrument P).bornWeight outcome rho := by sorry
