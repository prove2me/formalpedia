-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_tensorPower_productInput
-- name    : QEC.Semantics.FiniteInstrument.branchOperator_tensorPower_productInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:38.895957+00:00
-- url     : https://prove2.me/theorems/7359d37b-6420-4b8f-8ca5-814b1d2598ef
-- title:
--   Finite Instrument: branch Operator tensor Power product Input
-- statement:
--   Every observed tensor-power branch operator factors recursively on the
--   actual recursively tensorized product input density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L319-L347
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L319-L347

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.branchOperator_tensorPower_productInput
    (I : FiniteInstrument κ Ω H K) (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts),
      (I.tensorPower attempts).branchOperator history
          (tensorPowerProductInput rho rhoUnit attempts).toOperator =
        tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts history := by sorry
