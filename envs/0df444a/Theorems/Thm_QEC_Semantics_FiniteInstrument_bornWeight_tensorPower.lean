-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bornWeight_tensorPower
-- name    : QEC.Semantics.FiniteInstrument.bornWeight_tensorPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:27.519204+00:00
-- url     : https://prove2.me/theorems/4c717663-25c7-424c-814d-c1b2dcc6a592
-- title:
--   Finite Instrument: born Weight tensor Power
-- statement:
--   Observed tensor-power Born weights factor recursively on the actual
--   recursively tensorized input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L207-L226
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L207-L226

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
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

theorem QEC.Semantics.FiniteInstrument.bornWeight_tensorPower (I : FiniteInstrument κ Ω H K)
    (rho : DensityOperator H) (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory Ω attempts),
      (I.tensorPower attempts).bornWeight history
          (tensorPowerProductInput rho rhoUnit attempts) =
        tensorPowerBornProduct I rho attempts history
  := by sorry
