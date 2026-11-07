-- Prove2me | Theorems.Thm_QEC_Coding_PauliSymplectic_sum_positive_jointStabilizerBornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
-- name    : QEC.Coding.PauliSymplectic.sum_positive_jointStabilizerBornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:51:19.775318+00:00
-- url     : https://prove2.me/theorems/bdb37465-593d-4f7b-9f8b-4ce832e41ee5
-- title:
--   Pauli Symplectic: sum positive joint Stabilizer Born Weight smul conditional Density eq map Density to Operator
-- statement:
--   Positive-mass conditional joint-syndrome branches reconstruct the unconditioned
--   complete measurement channel; zero-mass outcomes are omitted only through the
--   generic proved zero-branch law.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L763-L775
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/Stabilizer/JointMeasurement.lean#L763-L775

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

theorem QEC.Coding.PauliSymplectic.sum_positive_jointStabilizerBornWeight_smul_conditionalDensity_eq_mapDensity_toOperator
    (checks : κ → Binary ι) (hcomm : ∀ left right, Commutes (checks left) (checks right))
    (rho : DensityOperator (Qubit.QubitRegister ι)) :
    (∑ syndrome : {syndrome : JointSyndrome κ //
        0 < (jointStabilizerInstrument checks hcomm).bornWeight syndrome rho},
      ((jointStabilizerInstrument checks hcomm).bornWeight syndrome.1 rho : Complex) •
        (jointStabilizerConditionalDensity checks hcomm syndrome.1 rho syndrome.2).toOperator) =
      (((jointStabilizerKrausFamily checks hcomm).toQuantumChannel
        (jointStabilizerKrausFamily_complete checks hcomm)).mapDensity rho).toOperator := by sorry
