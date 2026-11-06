-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_bindDependent_sum_bornWeight_eq_one
-- name    : QEC.Semantics.FiniteInstrument.bindDependent_sum_bornWeight_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:39:18.085208+00:00
-- url     : https://prove2.me/theorems/66fc1f08-123b-479f-a75e-0848797bd9ce
-- title:
--   Finite Instrument: bind Dependent sum born Weight eq one
-- statement:
--   Complete dependent sequential binding has normalized total observable Born mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L109-L115
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Sequential/DependentComposition.lean#L109-L115

import Definitions.Def_QEC_Semantics_Instruments_Sequential_Composition
import Definitions.Def_QEC_Semantics_Instruments_Sequential_DependentComposition
set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {κ₂ : Ω → Type x} [∀ outcome, Fintype (κ₂ outcome)]
variable {Ξ : Ω → Type y} [∀ outcome, Fintype (Ξ outcome)]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]

theorem QEC.Semantics.FiniteInstrument.bindDependent_sum_bornWeight_eq_one (I : FiniteInstrument κ Ω H K)
    (J : (outcome : Ω) → FiniteInstrument (κ₂ outcome) (Ξ outcome) K L)
    (hI : I.kraus.Complete)
    (hJ : ∀ outcome, (J outcome).kraus.Complete)
    (rho : DensityOperator H) :
    ∑ outcome, (I.bindDependent J).bornWeight outcome rho = 1 := by sorry
