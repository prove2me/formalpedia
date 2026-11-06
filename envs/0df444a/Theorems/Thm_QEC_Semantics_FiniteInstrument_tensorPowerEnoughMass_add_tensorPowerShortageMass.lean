-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerEnoughMass_add_tensorPowerShortageMass
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerEnoughMass_add_tensorPowerShortageMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:35:48.418373+00:00
-- url     : https://prove2.me/theorems/9c9e5ce3-76b5-4554-8a58-f418a0885b03
-- title:
--   Finite Instrument: tensor Power Enough Mass add tensor Power Shortage Mass
-- statement:
--   Completeness partitions all actual observed histories into enough and shortage mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L282-L299
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L282-L299

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerEnoughMass_add_tensorPowerShortageMass
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat) (rho : DensityOperator (tensorPowerCarrier H attempts))
    (hI : I.kraus.Complete) :
    I.tensorPowerEnoughMass accepts attempts required rho +
        I.tensorPowerShortageMass accepts attempts required rho = 1 := by sorry
