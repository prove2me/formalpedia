-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_branchOperator_punit
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_branchOperator_punit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:55:49.201699+00:00
-- url     : https://prove2.me/theorems/2e56e59b-69be-4f37-8991-d45600633e29
-- title:
--   Finite Instrument: bind Dependent branch Operator punit
-- statement:
--   When every second-stage observation is the unique `PUnit` value, the
--   retained first observed branch is sent through the complete second raw Kraus
--   map selected by that first outcome.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L246-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L246-L271

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator
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

theorem QEC.Semantics.FiniteInstrument.bindDependent_branchOperator_punit
    (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) PUnit K L)
    (outcome : Ω) (A : Operator H) :
    (I.bindDependent J).branchOperator ⟨outcome, PUnit.unit⟩ A =
      (J outcome).kraus.inducedMap (I.branchOperator outcome A) := by sorry
