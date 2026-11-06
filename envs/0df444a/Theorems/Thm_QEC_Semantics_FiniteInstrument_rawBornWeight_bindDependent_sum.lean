-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_rawBornWeight_bindDependent_sum
-- name    : QEC.Semantics.FiniteInstrument.rawBornWeight_bindDependent_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:36.153446+00:00
-- url     : https://prove2.me/theorems/72fe1f9f-eacd-45c2-997b-a7e3b7e34282
-- title:
--   Finite Instrument: raw Born Weight bind Dependent sum
-- statement:
--   Summing a CPTP dependent second stage over its actual raw fibre preserves each first raw mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L308-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L308-L330

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
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.rawBornWeight_bindDependent_sum (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) PUnit K L)
    (hJ : ∀ outcome, (J outcome).kraus.Complete) (rho : DensityOperator H)
    (firstIndex : κ) :
    ∑ secondIndex : κ₂ (I.observe firstIndex),
      (I.bindDependent J).rawBornWeight ⟨firstIndex, secondIndex⟩ rho =
        I.rawBornWeight firstIndex rho := by sorry
