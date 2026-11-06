-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
-- name    : QEC.Semantics.FiniteInstrument.tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:56:48.742475+00:00
-- url     : https://prove2.me/theorems/34544188-b3b2-4893-a359-421f0b69b789
-- title:
--   Finite Instrument: tensor Power Rejected First Moment eq attempts mul rejected Born Weight
-- statement:
--   Actual tensor-power rejection first moments are the number of trials times
--   the one-block Born mass of the actual non-accepted outcomes.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L131-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/FirstMoment.lean#L131-L253

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_FirstMoment
set_option autoImplicit false
universe u v w
open QEC
open QEC.Semantics
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument

theorem QEC.Semantics.FiniteInstrument.tensorPowerRejectedFirstMoment_eq_attempts_mul_rejectedBornWeight
    {κ : Type v} [Fintype κ] {Ω : Type w} [Fintype Ω] {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
    (I : FiniteInstrument κ Ω H K) (accepts : Ω → Prop) [DecidablePred accepts]
    (hI : I.kraus.Complete)
    (rho : DensityOperator H)
    (rhoUnit : DensityOperator (tensorPowerCarrier H 0)) :
    ∀ attempts : Nat,
      tensorPowerRejectedFirstMoment I accepts rho rhoUnit attempts =
        (attempts : ℝ) *
          ∑ outcome ∈ Finset.univ.filter (fun outcome => ¬ accepts outcome),
            I.bornWeight outcome rho
  := by sorry
