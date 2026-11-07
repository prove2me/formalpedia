-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_sum_stabilizerBornWeight_eq_one
-- name    : QEC.Coding.PauliSymplectic.sum_stabilizerBornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:45:29.336204+00:00
-- url     : https://prove2.me/theorems/de7c0737-df0b-450b-b76a-7a78d39c74dd
-- title:
--   Pauli Symplectic: sum stabilizer Born Weight eq one
-- statement:
--   The two binary stabilizer Born weights sum to one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L262-L268
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L262-L268

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

theorem QEC.Coding.PauliSymplectic.sum_stabilizerBornWeight_eq_one
    (P : Binary ι)
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    ∑ outcome : StabilizerOutcome,
        (stabilizerInstrument P).bornWeight outcome rho = 1 := by sorry
