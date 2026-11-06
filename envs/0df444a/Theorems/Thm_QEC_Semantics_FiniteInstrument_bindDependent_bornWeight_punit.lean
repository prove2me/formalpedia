-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_bornWeight_punit
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_bornWeight_punit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:25.760697+00:00
-- url     : https://prove2.me/theorems/7b390c18-7252-41ae-9f77-86f41cffaa61
-- title:
--   Finite Instrument: bind Dependent born Weight punit
-- statement:
--   Aggregating the unit-observed second stage recovers the original first observed Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L333-L375
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BornMass.lean#L333-L375

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

theorem QEC.Semantics.FiniteInstrument.bindDependent_bornWeight_punit (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) PUnit K L)
    (hJ : ∀ outcome, (J outcome).kraus.Complete) (outcome : Ω)
    (rho : DensityOperator H) :
    (I.bindDependent J).bornWeight ⟨outcome, PUnit.unit⟩ rho =
      I.bornWeight outcome rho := by sorry
