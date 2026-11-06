-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerShortageMass_markov_le_rejectedBornWeight
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerShortageMass_markov_le_rejectedBornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T14:07:39.48282+00:00
-- url     : https://prove2.me/theorems/0383dfd2-df97-4669-b25d-53b310a277c6
-- title:
--   Finite Instrument: tensor Power Shortage Mass markov le rejected Born Weight
-- statement:
--   A finite shortage event has Markov mass bounded by the actual rejected
--   first moment on the recursively tensorized product input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L257-L307
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L257-L307

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerShortageMass_markov_le_rejectedBornWeight
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (hI : I.kraus.Complete) (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0))
    (attempts required : Nat) (hrequired : required ≤ attempts) :
    ((attempts - required + 1 : Nat) : ℝ) *
        I.tensorPowerShortageMass accepts attempts required
          (tensorPowerProductInput rho rhoUnit attempts) ≤
      (attempts : ℝ) *
        ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
          I.bornWeight outcome rho := by sorry
