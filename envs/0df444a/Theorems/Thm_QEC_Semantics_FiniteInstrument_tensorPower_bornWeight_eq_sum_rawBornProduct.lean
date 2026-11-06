-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPower_bornWeight_eq_sum_rawBornProduct
-- name    : QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_eq_sum_rawBornProduct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:35:33.299734+00:00
-- url     : https://prove2.me/theorems/14194a80-6bdd-4d35-a5e9-87d0f0cac53e
-- title:
--   Finite Instrument: tensor Power born Weight eq sum raw Born Product
-- statement:
--   Observable tensor-power history mass is the finite regrouping of literal raw products.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L229-L245
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L229-L245

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

theorem QEC.Semantics.FiniteInstrument.tensorPower_bornWeight_eq_sum_rawBornProduct
    (I : FiniteInstrument κ Ω H K) (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) (attempts : Nat)
    (outcome : tensorPowerHistory Ω attempts) :
    (I.tensorPower attempts).bornWeight outcome
        (tensorPowerProductInput rho rhoUnit attempts) =
      ∑ rawHistory : tensorPowerHistory κ attempts,
        if (I.tensorPower attempts).observe rawHistory = outcome then
          tensorPowerRawBornProduct I rho attempts rawHistory
        else 0 := by sorry
