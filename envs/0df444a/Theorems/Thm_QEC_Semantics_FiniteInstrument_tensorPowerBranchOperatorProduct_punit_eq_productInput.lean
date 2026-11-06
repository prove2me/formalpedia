-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerBranchOperatorProduct_punit_eq_productInput
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerBranchOperatorProduct_punit_eq_productInput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:18.655982+00:00
-- url     : https://prove2.me/theorems/37c928cf-c5f9-4950-b5a1-a70ca862c1e8
-- title:
--   Finite Instrument: tensor Power Branch Operator Product punit eq product Input
-- statement:
--   If the sole visible outcome of every factor is `PUnit`, its recursive
--   branch product is exactly the recursive product of the complete one-factor
--   channel output.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProduct.lean#L50-L75
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/ChannelProduct.lean#L50-L75

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
import Definitions.Def_QEC_Semantics_Channels_Instrument
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProduct
set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
  [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.tensorPowerBranchOperatorProduct_punit_eq_productInput
    {κ : Type v} [Fintype κ]
    (I : FiniteInstrument κ PUnit H K) (hI : I.kraus.Complete)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (sigmaUnit : DensityOperator (tensorPowerCarrier K 0))
    (hunit : sigmaUnit.toOperator = rhoUnit.toOperator) :
    ∀ attempts : Nat,
      tensorPowerBranchOperatorProduct
          (fun outcome => I.branchOperator outcome rho.toOperator)
          rhoUnit.toOperator attempts
          (tensorPowerHistoryOf PUnit attempts (fun _ => PUnit.unit)) =
        (tensorPowerProductInput
          ((I.kraus.toQuantumChannel hI).mapDensity rho)
          sigmaUnit attempts).toOperator := by sorry
