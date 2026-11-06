-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_toFiniteInstrument_bindDependent_bornWeight
-- name    : QEC.Semantics.FiniteInstrument.toFiniteInstrument_bindDependent_bornWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:37:04.911688+00:00
-- url     : https://prove2.me/theorems/581d1cca-6ad1-4d88-bcae-295d0294e05e
-- title:
--   Finite Instrument: to Finite Instrument bind Dependent born Weight
-- statement:
--   Running a physical channel before an observed finite instrument evaluates
--   the latter's Born weight on the channel's actual output density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L304-L313
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/TensorPower/BranchOperator.lean#L304-L313

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
variable {κ' : Type x} [Fintype κ']
variable {L : Type u}
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.toFiniteInstrument_bindDependent_bornWeight
    (Phi : QuantumChannel H K) (J : FiniteInstrument κ' Ω K L)
    (outcome : Ω) (rho : DensityOperator H) :
    (Phi.toFiniteInstrument.bindDependent (fun _ => J)).bornWeight
        ⟨PUnit.unit, outcome⟩ rho =
      J.bornWeight outcome (Phi.mapDensity rho) := by sorry
