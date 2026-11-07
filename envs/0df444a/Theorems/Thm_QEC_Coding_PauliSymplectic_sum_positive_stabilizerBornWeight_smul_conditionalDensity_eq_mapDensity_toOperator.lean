-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_sum_positive_stabilizerBornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
-- name    : QEC.Coding.PauliSymplectic.sum_positive_stabilizerBornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:44:49.446635+00:00
-- url     : https://prove2.me/theorems/fbbdf86a-3388-4d7e-be8e-177bbac1477b
-- title:
--   Pauli Symplectic: sum positive stabilizer Born Weight smul conditional Density eq map Density to Operator
-- statement:
--   Positive-mass conditional branches reconstruct the unconditioned complete
--   stabilizer channel; zero-mass outcomes are omitted only through the generic
--   proved zero-branch law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L305-L316
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/Measurement.lean#L305-L316

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

theorem QEC.Coding.PauliSymplectic.sum_positive_stabilizerBornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
    (P : Binary ι)
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    (∑ outcome : {outcome : StabilizerOutcome //
        0 < (stabilizerInstrument P).bornWeight outcome rho},
      ((stabilizerInstrument P).bornWeight outcome.1 rho : Complex) •
        (stabilizerConditionalDensity P outcome.1 rho outcome.2).toOperator) =
      (((stabilizerKrausFamily P).toQuantumChannel
        (stabilizerKrausFamily_complete P)).mapDensity rho).toOperator := by sorry
