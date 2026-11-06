-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBornWeight_tensorPower
-- name    : QEC.Semantics.FiniteInstrument.rawBornWeight_tensorPower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:20.942667+00:00
-- url     : https://prove2.me/theorems/2a8eee37-9a6d-4491-8a2c-5fc81c7fa7a9
-- title:
--   Finite Instrument: raw Born Weight tensor Power
-- statement:
--   Literal tensor-power raw weights equal their recursively factored products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L171-L195
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L171-L195

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

theorem QEC.Semantics.FiniteInstrument.rawBornWeight_tensorPower (I : FiniteInstrument κ Ω H K)
    (rho : DensityOperator H) (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ (attempts : Nat) (history : tensorPowerHistory κ attempts),
      (I.tensorPower attempts).rawBornWeight history
          (tensorPowerProductInput rho rhoUnit attempts) =
        tensorPowerRawBornProduct I rho attempts history
  := by sorry
