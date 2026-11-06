-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerHistoryConditionedInstrument_bornWeight_eq_tensorPower_bornWeight
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_bornWeight_eq_tensorPower_bornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:35:58.227952+00:00
-- url     : https://prove2.me/theorems/b1fb8fa4-8f86-4858-8a17-62640f2d56d4
-- title:
--   Finite Instrument: tensor Power History Conditioned Instrument born Weight eq tensor Power born Weight
-- statement:
--   The total selected-or-replacement instrument preserves each actual first observed history mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L380-L406
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L380-L406

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

theorem QEC.Semantics.FiniteInstrument.tensorPowerHistoryConditionedInstrument_bornWeight_eq_tensorPower_bornWeight
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω]
    (I : FiniteInstrument κ Ω H (Qubit.QubitRegister ι))
    (accepts : Ω → Prop) [DecidablePred accepts]
    (attempts required : Nat)
    (shortageState : DensityOperator (Qubit.QubitRegister (Fin required × ι)))
    (history : tensorPowerHistory Ω attempts)
    (rho : DensityOperator (tensorPowerCarrier H attempts)) :
    (tensorPowerHistoryConditionedInstrument I accepts attempts required shortageState).bornWeight
        ⟨history, PUnit.unit⟩ rho =
      (I.tensorPower attempts).bornWeight history rho := by sorry
